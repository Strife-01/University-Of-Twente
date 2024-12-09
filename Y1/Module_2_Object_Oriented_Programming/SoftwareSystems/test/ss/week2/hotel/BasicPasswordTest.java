package ss.week2.hotel;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertFalse;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import ss.hotel.password.BasicPassword;

/**
 * Test program for Password. Lab exercise Software Systems
 * @author Arend Rensink, Jip Spel
 */
public class BasicPasswordTest {
	/** Test variable for a <tt>Password</tt> object. */
	private BasicPassword pass;

	/**
	 * Sets the instance variable <tt>pass</tt> to a well-defined initial value.
	 */
	@BeforeEach
	public void setUp() {
		pass = new BasicPassword();
	}

	/**
	 * Test the method <tt>acceptable(suggestion)</tt>.
	 */
    @Test
	public void testAcceptable() {
		assertFalse(pass.acceptable("no"));
		assertFalse(pass.acceptable("no nono"));
        assertFalse(pass.acceptable("no no"));
		assertTrue(pass.acceptable("yesyesyes"));
	}

    /**
	 * Test the method <tt>testWord</tt>.
	 */
    @Test
	public void testTestWord() {
		assertFalse(pass.testWord("wrong"));
		assertTrue(pass.testWord(new String(BasicPassword.INITIAL)));
	}

	/**
	 * Test the method <tt>setWord</tt> with a wrong old password.
	 */
    @Test
	public void testSetWordWrongOld() {
		String wrongOldPassowrd = "wrongwrong";
		String newPassword = "yesyesyes";
		assertFalse(pass.setWord(wrongOldPassowrd, newPassword));
		assertTrue(pass.testWord(BasicPassword.INITIAL));
		assertFalse(pass.testWord(newPassword));
	}

	/**
	 * Test the method <tt>setWord</tt> with an unacceptable new password.
	 */
    @Test
	public void testSetWordWrongNew() {
		String wrongNew = "no no";
		assertFalse(pass.setWord(BasicPassword.INITIAL, wrongNew));
		assertTrue(pass.testWord(BasicPassword.INITIAL));
		assertFalse(pass.testWord(wrongNew));
	}

	/**
	 * Test the method <tt>setWord</tt> for correct usage.
	 */
    @Test
	public void testSetWordOkay() {
		String newpass = "yesyesyes";
		assertTrue(pass.setWord(BasicPassword.INITIAL, newpass));
		assertFalse(pass.testWord(BasicPassword.INITIAL));
		assertTrue(pass.testWord(newpass));
	}
}
