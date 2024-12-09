package nl.utwente.jmlplugin.runtime;

import com.intellij.compiler.CompilerConfiguration;
import com.intellij.openapi.application.Application;
import com.intellij.openapi.application.ApplicationManager;
import com.intellij.openapi.compiler.options.ExcludeEntryDescription;
import com.intellij.openapi.compiler.options.ExcludesConfiguration;
import com.intellij.openapi.module.Module;
import com.intellij.openapi.module.ModuleManager;
import com.intellij.openapi.project.Project;
import com.intellij.openapi.roots.*;
import com.intellij.openapi.util.ThrowableComputable;
import com.intellij.openapi.util.Trinity;
import com.intellij.openapi.vfs.*;
import com.intellij.psi.PsiManager;
import com.intellij.task.BuildTask;
import com.intellij.task.ProjectTask;
import com.intellij.task.ProjectTaskContext;
import com.intellij.task.ProjectTaskRunner;
import com.intellij.task.impl.ProjectTaskList;
import nl.utwente.jmlplugin.settings.JMLApplicationSettings;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.concurrency.Promise;

import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;

/**
 * This class is responsible for detecting
 * when a build is going to take place
 * so we can insert runtime checks.
 * <p>
 * A problem we run into is that CompileTask,
 * the API you would normally use for this,
 * triggers too late in the build process
 * to affect which files are compiled.
 * Instead, to detect build tasks, we abuse the
 * ProjectTaskRunner API by pretending to be
 * a potential runner for the build task.
 * When we are asked if we can run the build task,
 * we prepare the project and then return false.
 */
public class JMLBuildListener extends ProjectTaskRunner {

    /**
     * Detects build tasks and prepares the project.
     *
     * @param project     The project that is affected by this task
     * @param projectTask The task that is about to be run
     * @return False, because this class cannot run the build task
     */
    @Override
    public boolean canRun(@NotNull Project project, @NotNull ProjectTask projectTask) {
        if (!JMLApplicationSettings.getInstance().RUNTIME_CHECKING_ENABLED) {
            return false;
        }

        // Check whether we are trying to perform a build
        if (!(projectTask instanceof BuildTask) && !(projectTask instanceof ProjectTaskList)) {
            return false;
        }
        if (projectTask instanceof ProjectTaskList) {
            boolean hasBuildTask = false;
            for (ProjectTask innerTask : (ProjectTaskList) projectTask) {
                if (innerTask instanceof BuildTask) {
                    hasBuildTask = true;
                    break;
                }
            }
            if (!hasBuildTask) {
                return false;
            }
        }

        // Initialize some variables outside the loop to prevent unnecessary recalculation
        ExcludesConfiguration excludesConfiguration = CompilerConfiguration.getInstance(project)
                .getExcludedEntriesConfiguration();
        Application application = ApplicationManager.getApplication();
        PsiManager psiManager = PsiManager.getInstance(project);

        /*
        The project file structure is as follows:

        A Project can consist of multiple Modules.
        Each Module can have multiple ContentEntries.
        Projects and Modules do not describe locations
        for project files, only ContentEntries do.
        Each ContentEntry has a single root folder
        (this folder can be anywhere, even on a remote server)
        and can have multiple SourceFolders
        and ExcludeFolders located under this root.
         */
        for (Module module : ModuleManager.getInstance(project).getModules()) {
            for (ContentEntry entry : ModuleRootManager.getInstance(module).getContentEntries()) {
                VirtualFile entryVF = entry.getFile();
                if (entryVF == null) {
                    continue;
                }

                // Relativize all sources
                // <relative path, is test source, package prefix>
                List<Trinity<String, Boolean, String>> relativeSources = new ArrayList<>();
                for (SourceFolder source : entry.getSourceFolders()) {
                    VirtualFile sourceVF = source.getFile();
                    if (sourceVF == null) {
                        continue;
                    }
                    String relativePath = VfsUtil.getRelativePath(sourceVF, entryVF);
                    if (relativePath == null) {
                        continue;
                    }
                    relativeSources.add(Trinity.create(relativePath, source.isTestSource(), source.getPackagePrefix()));
                }

                // Relativize all excludes
                List<String> relativeExcludes = new ArrayList<>();
                for (ExcludeFolder exclude : entry.getExcludeFolders()) {
                    VirtualFile excludeVF = exclude.getFile();
                    if (excludeVF == null) {
                        continue;
                    }
                    String relativePath = VfsUtil.getRelativePath(excludeVF, entryVF);
                    if (relativePath == null) {
                        continue;
                    }
                    relativeExcludes.add(relativePath);
                }

                // Exclude all files in the original ContentEntry
                excludesConfiguration.addExcludeEntryDescription(
                        new ExcludeEntryDescription(entryVF, true, false, module));

                // Copy all files in the original ContentEntry into a temporary directory and insert runtime checks
                VirtualFile tempVF;
                try {
                    // This originally used FileUtilRt.createTempDirectory(), but that resulted in weird errors
                    tempVF = VfsUtil.findFile(Files.createTempDirectory("runtime-checking"), true);
                    if (tempVF == null) {
                        continue;
                    }
                    application.runWriteAction((ThrowableComputable<Void, IOException>) () -> {
                        JMLRuntimeCheckingUtil.copyAndProcess(
                                entryVF, tempVF, psiManager, JMLRuntimeCheckInserter::insertRuntimeChecks);
                        return null; // Meaningless, but there is no ThrowableRunnable variant of runWriteAction()
                    });
                } catch (IOException e) {
                    continue;
                }

                // Create a new ContentEntry for the temporary directory
                ModuleRootModificationUtil.updateModel(module, model -> {
                    ContentEntry tempEntry = model.addContentEntry(tempVF);
                    tempVF.putUserData(JMLRuntimeCheckingUtil.RUNTIME_CHECKING_MARKER, true);
                    for (Trinity<String, Boolean, String> source : relativeSources) {
                        VirtualFile sourceVF = VfsUtil.findRelativeFile(source.getFirst(), tempVF);
                        if (sourceVF == null) {
                            continue;
                        }
                        tempEntry.addSourceFolder(sourceVF, source.getSecond(), source.getThird());
                    }
                    for (String exclude : relativeExcludes) {
                        VirtualFile excludeVF = VfsUtil.findRelativeFile(exclude, tempVF);
                        if (excludeVF == null) {
                            continue;
                        }
                        tempEntry.addExcludeFolder(excludeVF);
                    }
                    tempEntry.setExcludePatterns(entry.getExcludePatterns());
                });
            }
        }

        return false;
    }

    /**
     * Should never be called
     * (the other canRun method should be used instead).
     * <p>
     * Throws an exception instead of failing silently
     * to make catching bugs easier.
     */
    @Override
    public boolean canRun(@NotNull ProjectTask projectTask) {
        throw new NullPointerException("Project is null");
    }

    /**
     * Should never be called.
     * <p>
     * Throws an exception instead of failing silently
     * to make catching bugs easier.
     */
    @Override
    public Promise<Result> run(@NotNull Project project,
                               @NotNull ProjectTaskContext context,
                               ProjectTask @NotNull ... tasks) {
        throw new UnsupportedOperationException("JMLBuildListener was asked to run a task");
    }

}
