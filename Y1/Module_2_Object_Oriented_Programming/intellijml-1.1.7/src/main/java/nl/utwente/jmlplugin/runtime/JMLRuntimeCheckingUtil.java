package nl.utwente.jmlplugin.runtime;

import com.intellij.openapi.util.Key;
import com.intellij.openapi.vfs.VirtualFile;
import com.intellij.psi.PsiFile;
import com.intellij.psi.PsiManager;

import java.io.IOException;
import java.util.function.Consumer;

/**
 * Constants and utility methods for runtime checking.
 */
public class JMLRuntimeCheckingUtil {

    public static final Key<Boolean> RUNTIME_CHECKING_MARKER = Key.create("RUNTIME_CHECKING_MARKER");

    // Used by copyAndProcess() to mark file write requests
    private static final Object REQUESTOR = new Object();

    private JMLRuntimeCheckingUtil() {
    }

    /**
     * Copies a directory and all its contents
     * to another directory.
     * <p>
     * After copying, each VirtualFile is converted
     * to a PsiFile using the given PsiManager
     * and passed on to the fileProcessor.
     * The fileProcessor may then edit the tree.
     * <p>
     * This method writes files and must therefore
     * be executed inside an IntelliJ write action.
     * <p>
     * Implementation adapted from VfsUtil.copyDirectory().
     *
     * @param from          The directory to copy from
     * @param to            The directory to copy to
     * @param psiManager    The manager to use to convert VirtualFiles to PsiFiles
     * @param fileProcessor The function to process copied files
     * @throws IOException For generic I/O problems
     */
    public static void copyAndProcess(VirtualFile from, VirtualFile to,
                                      PsiManager psiManager, Consumer<PsiFile> fileProcessor) throws IOException {
        for (VirtualFile child : from.getChildren()) {
            String childName = child.getName();
            if (child.isDirectory()) {
                copyAndProcess(child, to.createChildDirectory(REQUESTOR, childName), psiManager, fileProcessor);
                continue;
            }
            // VfsUtilCore.copyFile() is not safe here, that method has a hidden file size limit of 20MB
            VirtualFile copy = child.copy(REQUESTOR, to, childName);
            PsiFile psiFile = psiManager.findFile(copy);
            if (psiFile != null) {
                fileProcessor.accept(psiFile);
            }
        }
    }

}
