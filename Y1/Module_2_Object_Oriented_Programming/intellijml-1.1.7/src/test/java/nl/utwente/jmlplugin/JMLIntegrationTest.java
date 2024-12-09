package nl.utwente.jmlplugin;

import com.intellij.openapi.roots.LanguageLevelProjectExtension;
import com.intellij.openapi.vfs.VirtualFile;
import com.intellij.pom.java.LanguageLevel;
import com.intellij.testFramework.fixtures.JavaCodeInsightFixtureTestCase;

/**
 * Does an integration test on the annotators
 */
public class JMLIntegrationTest extends JavaCodeInsightFixtureTestCase {

    @Override
    protected String getTestDataPath() {
        return "src/test/integrationTestData";
    }

    @Override
    protected void setUp() throws Exception {
        super.setUp();
        LanguageLevelProjectExtension.getInstance(getProject()).setLanguageLevel(LanguageLevel.JDK_11);
    }

    public void testBox() {
        myFixture.configureByFile("Box.java");
        myFixture.checkHighlighting(true, false, true, false);
    }

    public void testStorageSpace() {
        myFixture.copyDirectoryToProject(".", "integrationTestData");
        myFixture.allowTreeAccessForFile(myFixture.findFileInTempDir("integrationTestData/Box.java"));
        myFixture.openFileInEditor(myFixture.findFileInTempDir("integrationTestData/StorageSpace.java"));
        myFixture.checkHighlighting(true, false, true, false);
    }

}
