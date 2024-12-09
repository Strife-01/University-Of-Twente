package nl.utwente.jmlplugin.runtime;

import com.intellij.compiler.CompilerConfiguration;
import com.intellij.openapi.command.WriteCommandAction;
import com.intellij.openapi.compiler.CompileContext;
import com.intellij.openapi.compiler.CompileTask;
import com.intellij.openapi.compiler.options.ExcludeEntryDescription;
import com.intellij.openapi.compiler.options.ExcludesConfiguration;
import com.intellij.openapi.module.Module;
import com.intellij.openapi.module.ModuleManager;
import com.intellij.openapi.project.Project;
import com.intellij.openapi.roots.ContentEntry;
import com.intellij.openapi.roots.ModuleRootModificationUtil;
import com.intellij.openapi.vfs.VirtualFile;
import nl.utwente.jmlplugin.settings.JMLApplicationSettings;

import java.io.IOException;

/**
 * Responsible for cleaning up the changes we make
 * to the project's configuration for runtime checking.
 */
public class JMLRuntimeCheckingCleaner implements CompileTask {

    /**
     * Performs the cleanup of a project.
     *
     * @param context The context of the current compilation
     * @return True, to indicate that we allow the build to succeed
     */
    @Override
    public boolean execute(CompileContext context) {
        if (!JMLApplicationSettings.getInstance().RUNTIME_CHECKING_ENABLED) {
            return true;
        }
        Project project = context.getProject();
        ExcludesConfiguration excludesConfiguration = CompilerConfiguration.getInstance(project)
                .getExcludedEntriesConfiguration();
        for (Module module : ModuleManager.getInstance(project).getModules()) {
            ModuleRootModificationUtil.updateModel(module, model -> {
                for (ContentEntry entry : model.getContentEntries()) {
                    VirtualFile entryVF = entry.getFile();
                    if (entryVF == null) {
                        continue;
                    }
                    if (entryVF.getUserData(JMLRuntimeCheckingUtil.RUNTIME_CHECKING_MARKER) != null) {
                        model.removeContentEntry(entry);
                        try {
                            WriteCommandAction.writeCommandAction(project)
                                    .withName("Runtime Checking Cleanup")
                                    .run(() -> entryVF.delete(this));
                        } catch (IOException e) {
                            continue;
                        }
                        continue;
                    }
                    // This works because the new ExcludeEntryDescription equals() the existing one
                    excludesConfiguration.removeExcludeEntryDescription(
                            new ExcludeEntryDescription(entryVF, true, false, module));
                }
            });
        }
        return true;
    }

}
