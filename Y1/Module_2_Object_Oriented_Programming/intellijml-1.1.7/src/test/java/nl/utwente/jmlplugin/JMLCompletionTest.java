package nl.utwente.jmlplugin;

import java.util.Arrays;
import java.util.List;
import com.intellij.codeInsight.completion.CompletionType;
import com.intellij.testFramework.fixtures.LightJavaCodeInsightFixtureTestCase;

import static nl.utwente.jmlplugin.completion.JMLCompletionUtils.*;
import static nl.utwente.jmlplugin.psi.JMLTokenSet.*;

/**
 * Test for the code completion part of the plugin.
 *
 * The way to make the tests is by writing a java class in the completionTestData folder that has some
 * JML for which you would like to test the completion on, then at the place that the completion should be invoked
 * at put the "<caret>" symbol there and the test will invoke the completion there.
 *
 * The test will return you a list of string suggestions that the autocomplete gave, you can then check whether this was
 * the expected list or contains the expected elements.
 *
 * Many tests are duplicated to check the completion with and without a semicolon as the parser has issues with incomplete
 * expressions and like to throw error elements that completely screw up the parse tree structure where the completion is
 * supposed to take place, this makes it a giant pain to deal with and custom handling of these circumstances is necessary,
 * hence the tests must also test with a semicolon and without one.
 *
 * There is also some boiler plate that needs to be copy pasted in the test method itself, but you can look that up below.
 */

public class JMLCompletionTest extends LightJavaCodeInsightFixtureTestCase {

    public static List<String> START_KEYWORDS = Arrays.asList(getText(methodSpecCaseKeywords));
    public static List<String> METHOD_MODIFIERS = Arrays.asList(getText(methodDeclModifiers));
    public static List<String> ALSO = Arrays.asList(getText(also));

    @Override
    protected String getTestDataPath() {
        return "src/test/completionTestData";
    }

    public void testStartingJMLKeywords() {
        myFixture.configureByFile("JMLStartingKeywords.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.containsAll(START_KEYWORDS));
        assertTrue(strings.containsAll(METHOD_MODIFIERS));
        assertTrue(strings.containsAll(ALSO));
        assertEquals(START_KEYWORDS.size() + METHOD_MODIFIERS.size() + ALSO.size(), strings.size());
    }

    public void testJMLJavaField() {
        myFixture.configureByFile("JavaField.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("number"));
    }

    public void testJMLJavaFieldSemicolon() {
        myFixture.configureByFile("JavaFieldSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("number"));
    }

    public void testMethodParameters() {
        myFixture.configureByFile("MethodParameter.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("methodParameter"));
    }

    public void testMethodParameterSemicolon() {
        myFixture.configureByFile("MethodParameterSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("methodParameter"));
    }

    public void testMethod() {
        myFixture.configureByFile("Method.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("randomNumber"));
    }

    public void testMethodSemicolon() {
        myFixture.configureByFile("MethodSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("randomNumber"));
    }

    public void testStaticImports() {
        myFixture.configureByFile("StaticImports.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("MAX_VALUE"));
        assertTrue(strings.contains("getInteger"));
    }

    public void testStaticImportsSemicolon() {
        myFixture.configureByFile("StaticImportsSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("MAX_VALUE"));
        assertTrue(strings.contains("getInteger"));
    }

    public void testDotCompletion() {
        myFixture.configureByFile("DotCompletion.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("add"));
    }

    public void testDotCompletionSemicolon() {
        myFixture.configureByFile("DotCompletionSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("add"));
    }

    public void testStaticDotCompletion() {
        myFixture.configureByFile("StaticDot.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("MAX_VALUE"));
        assertTrue(strings.contains("getInteger"));
    }

    public void testStaticDotCompletionSemicolon() {
        myFixture.configureByFile("StaticDotSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("MAX_VALUE"));
        assertTrue(strings.contains("getInteger"));
    }

    public void testSignalsCompletion() {
        myFixture.configureByFile("Signals.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("IllegalStateException"));
    }

    public void testSignalsCompletionSemicolon() {
        myFixture.configureByFile("SignalsSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("IllegalStateException"));
    }

    public void testThis() {
        myFixture.configureByFile("This.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("privateNum"));
        assertTrue(strings.contains("protectedNum"));
        assertTrue(strings.contains("publicNum"));
        assertTrue(strings.contains("defaultNum"));
        assertTrue(strings.contains("getPrivateNum"));
        assertTrue(strings.contains("getProtectedNum"));
        assertTrue(strings.contains("getPublicNum"));
        assertTrue(strings.contains("getDefaultNum"));
    }

    public void testThisSemicolon() {
        myFixture.configureByFile("ThisSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("privateNum"));
        assertTrue(strings.contains("protectedNum"));
        assertTrue(strings.contains("publicNum"));
        assertTrue(strings.contains("defaultNum"));
        assertTrue(strings.contains("getPrivateNum"));
        assertTrue(strings.contains("getProtectedNum"));
        assertTrue(strings.contains("getPublicNum"));
        assertTrue(strings.contains("getDefaultNum"));
    }

    /**
     * Had to use a standard library abstract class to test as the testing framework
     * just can not properly load custom classes to test the super completion properly.
     * (or there might be an issue with the order of the class loading, but I can' be sure)
     */
    public void testSuper() {
        myFixture.configureByFile(  "Super.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("get"));
        assertTrue(strings.contains("size"));
        assertTrue(strings.contains("modCount"));
        assertTrue(strings.contains("wait"));
    }

    public void testSuperSemicolon() {
        myFixture.configureByFile(  "SuperSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("get"));
        assertTrue(strings.contains("size"));
        assertTrue(strings.contains("modCount"));
        assertTrue(strings.contains("wait"));
    }

    public void testAssignable() {
        myFixture.configureByFile(  "Assignable.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("number"));
        assertTrue(strings.contains("\\nothing"));
        assertTrue(strings.contains("\\everything"));
    }

    public void testAssignableSemicolon() {
        myFixture.configureByFile(  "AssignableSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("number"));
        assertTrue(strings.contains("\\nothing"));
        assertTrue(strings.contains("\\everything"));
    }

    public void testModifiable() {
        myFixture.configureByFile(  "Modifiable.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("number"));
        assertTrue(strings.contains("\\nothing"));
        assertTrue(strings.contains("\\everything"));
    }

    public void testModifiableSemicolon() {
        myFixture.configureByFile(  "ModifiableSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("number"));
        assertTrue(strings.contains("\\nothing"));
        assertTrue(strings.contains("\\everything"));
    }

    public void testModifies() {
        myFixture.configureByFile(  "Modifies.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("number"));
        assertTrue(strings.contains("\\nothing"));
        assertTrue(strings.contains("\\everything"));
    }

    public void testModifiesSemicolon() {
        myFixture.configureByFile(  "ModifiesSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("number"));
        assertTrue(strings.contains("\\nothing"));
        assertTrue(strings.contains("\\everything"));
    }

    public void testResultDot() {
        myFixture.configureByFile(  "ResultDot.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("add"));
        assertTrue(strings.contains("addAll"));
    }

    public void testResultDotSemicolon() {
        myFixture.configureByFile(  "ResultDotSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("add"));
        assertTrue(strings.contains("addAll"));
    }

    public void testOldDot() {
        myFixture.configureByFile(  "OldDot.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("add"));
        assertTrue(strings.contains("addAll"));
    }

    public void testOldDotSemicolon() {
        myFixture.configureByFile(  "OldDotSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("add"));
        assertTrue(strings.contains("addAll"));
    }

    public void testQuantifiedInitializeSection() {
        myFixture.configureByFile(  "QuantifiedInitialization.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.containsAll(Arrays.asList(PRIMITIVE_TYPES)));
    }

    public void testQuantifiedInitializeSectionSemicolon() {
        myFixture.configureByFile(  "QuantifiedInitializationSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.containsAll(Arrays.asList(PRIMITIVE_TYPES)));
    }

    public void testQuantifiedCondition() {
        myFixture.configureByFile(  "QuantifiedCondition.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("fieldInt"));
        assertTrue(strings.contains("getRandomNumber"));
    }

    public void testQuantifiedConditionSemicolon() {
        myFixture.configureByFile(  "QuantifiedConditionSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("fieldInt"));
        assertTrue(strings.contains("getRandomNumber"));
    }

    public void testQuantifiedLastSection() {
        myFixture.configureByFile(  "QuantifiedLastSection.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("fieldInt"));
        assertTrue(strings.contains("getSomeNumber"));
    }

    public void testQuantifiedLastSectionSemicolon() {
        myFixture.configureByFile(  "QuantifiedLastSectionSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("fieldInt"));
        assertTrue(strings.contains("getSomeNumber"));
    }

    public void testStarStaticImport() {
        myFixture.configureByFile(  "SpecificStaticImport.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("MAX_VALUE"));
        assertFalse(strings.contains("getInteger"));
    }

    public void testStarStaticImportSemicolon() {
        myFixture.configureByFile(  "SpecificStaticImportSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();
        assertTrue(strings.contains("MAX_VALUE"));
        assertFalse(strings.contains("getInteger"));
    }

    public void testResult() {
        myFixture.configureByFile(  "Result.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("\\result"));
    }

    public void testResultSemicolon() {
        myFixture.configureByFile(  "ResultSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("\\result"));
    }

    public void testOld() {
        myFixture.configureByFile(  "Old.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("\\old()"));
    }

    public void testOldSemicolon() {
        myFixture.configureByFile(  "OldSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("\\old()"));
    }

    public void testIdentifierClassName() {
        myFixture.configureByFile(  "IdentifierClassName.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("Integer"));
        assertTrue(strings.contains("InterruptedException"));
    }

    public void testIdentifierClassNameSemicolon() {
        myFixture.configureByFile(  "IdentifierClassNameSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("Integer"));
        assertTrue(strings.contains("InterruptedException"));
    }

    public void testClassInvariant() {
        myFixture.configureByFile(  "ClassInvariant.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("public"));
        assertTrue(strings.contains("protected"));
        assertTrue(strings.contains("private"));
        assertTrue(strings.contains("static"));
        assertTrue(strings.contains("invariant"));
        assertTrue(strings.contains("instance"));
    }

    public void testClassInvariantSemicolon() {
        myFixture.configureByFile(  "ClassInvariantSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("public"));
        assertTrue(strings.contains("protected"));
        assertTrue(strings.contains("private"));
        assertTrue(strings.contains("static"));
        assertTrue(strings.contains("invariant"));
        assertTrue(strings.contains("instance"));
    }

    public void testFieldModifiers() {
        myFixture.configureByFile(  "FieldModifiers.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("instance"));
        assertTrue(strings.contains("nullable"));
        assertTrue(strings.contains("spec_protected"));
        assertTrue(strings.contains("spec_public"));
    }

    public void testFieldModifiersSemicolon() {
        myFixture.configureByFile(  "FieldModifiersSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("instance"));
        assertTrue(strings.contains("nullable"));
        assertTrue(strings.contains("spec_protected"));
        assertTrue(strings.contains("spec_public"));
    }

    public void testNestedClass() {
        myFixture.configureByFile(  "NestedClass.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("publicInt"));
        assertTrue(strings.contains("protectedInt"));
        assertTrue(strings.contains("defaultInt"));
        assertTrue(strings.contains("privateInt"));
        assertTrue(strings.contains("getPublicInt"));
        assertTrue(strings.contains("getProtectedInt"));
        assertTrue(strings.contains("defaultInt"));
        assertTrue(strings.contains("privateInt"));
        assertTrue(strings.contains("innerClassInt"));
    }

    public void testNestedClassSemicolon() {
        myFixture.configureByFile(  "NestedClassSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("publicInt"));
        assertTrue(strings.contains("protectedInt"));
        assertTrue(strings.contains("defaultInt"));
        assertTrue(strings.contains("privateInt"));
        assertTrue(strings.contains("getPublicInt"));
        assertTrue(strings.contains("getProtectedInt"));
        assertTrue(strings.contains("defaultInt"));
        assertTrue(strings.contains("privateInt"));
        assertTrue(strings.contains("innerClassInt"));
    }

    public void testComplexDot() {
        myFixture.configureByFile(  "ComplexDot.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("trim"));
        assertTrue(strings.contains("charAt"));
        assertTrue(strings.contains("length"));
    }

    public void testComplexDotSemicolon() {
        myFixture.configureByFile(  "ComplexDotSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("trim"));
        assertTrue(strings.contains("charAt"));
        assertTrue(strings.contains("length"));
    }

    /**
     * Code block assert also tests the completion for loop_invariant.
     */
    public void testCodeBlockAssert() {
        myFixture.configureByFile(  "CodeBlock.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("number"));
        assertTrue(strings.contains("num"));
        assertTrue(strings.contains("getRandomNumber"));
        assertTrue(strings.contains("visible"));
        assertFalse(strings.contains("notVisible"));
    }

    public void testCodeBlockAssertSemicolon() {
        myFixture.configureByFile(  "CodeBlockSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("number"));
        assertTrue(strings.contains("num"));
        assertTrue(strings.contains("getRandomNumber"));
        assertTrue(strings.contains("visible"));
        assertFalse(strings.contains("notVisible"));
    }

    public void testMixedJMLJavaDot() {
        myFixture.configureByFile(  "MixedJMLJavaDot.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("trim"));
        assertTrue(strings.contains("length"));
    }

    public void testMixedJMLJavaDotSemicolon() {
        myFixture.configureByFile(  "MixedJMLJavaDotSemicolon.java");
        myFixture.complete(CompletionType.BASIC, 1);

        List<String> strings = myFixture.getLookupElementStrings();
        if (strings == null) fail();

        assertTrue(strings.contains("trim"));
        assertTrue(strings.contains("length"));
    }


}
