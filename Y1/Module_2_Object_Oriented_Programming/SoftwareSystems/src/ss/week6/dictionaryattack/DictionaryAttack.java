package ss.week6.dictionaryattack;

import org.apache.commons.codec.DecoderException;
import org.apache.commons.codec.binary.Hex;

import java.awt.image.BufferedImage;
import java.io.*;
import java.math.BigInteger;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;


public class DictionaryAttack {
	private Map<String, String> passwordMap;
	private Map<String, String> hashDictionary;

	/**
	 * Reads a password file. Each line of the password file has the form:
	 * username: encodedpassword
	 * 
	 * After calling this method, the passwordMap class variable should be
	 * filled with the content of the file. The key for the map should be
	 * the username, and the password hash should be the content.
	 * @param filename
	 * @throws IOException
	 */
	public void readPasswords(String filename) throws IOException {
		Reader reader;
		try {
			reader = new FileReader(filename);
		} catch (FileNotFoundException e) {
			throw new IOException(e);
		}
		BufferedReader bufferedReader = new BufferedReader(reader);
		passwordMap = new HashMap<String, String>();
		while(bufferedReader.ready()) {
			String line = bufferedReader.readLine();
			String[] content = line.split(": ");
			passwordMap.put(content[0], content[1]);
		}
		bufferedReader.close();
		reader.close();
	}

	/**
	 * Given a password, return the MD5 hash of a password. The resulting
	 * hash (or sometimes called digest) should be hex-encoded in a String.
	 * @param password
	 * @return
	 */
	public String getPasswordHash(String password) {
		MessageDigest md;
		try {
            md = MessageDigest.getInstance("MD5");
        } catch (NoSuchAlgorithmException e) {
            System.out.println("This algorithm doesn't exist.");
			return null;
        }
		md.update(password.getBytes());
		byte[] digest = md.digest();
        StringBuilder hex = new StringBuilder();
		for (byte i : digest) {
			hex.append(String.format("%02X", i));
		}
		return new String(hex).toLowerCase();
    }
	/**
	 * Checks the password for the user the password list. If the user
	 * does not exist, returns false.
	 * @param user
	 * @param password
	 * @return whether the password for that user was correct.
	 */
	public boolean checkPassword(String user, String password) {
		if (user == null) {
			return false;
		}
		String userHash = passwordMap.get(user);
		String passwordHash = getPasswordHash(password);
		return userHash.equals(passwordHash);
	}

	/**
	 * Reads a dictionary from file (one line per word) and use it to add
	 * entries to a dictionary that maps password hashes (hex-encoded) to
     * the original password.
	 * @param filename filename of the dictionary.
	 */
    	public void addToHashDictionary(String filename) {
			hashDictionary = new HashMap<String, String>();
			Reader reader;
			try {
                reader = new FileReader(filename);
            } catch (FileNotFoundException e) {
                System.out.println(filename + " doesn't exist!");
				return;
            }

			BufferedReader bufferedReader = new BufferedReader(reader);
			while (true) {
                try {
                    if (!bufferedReader.ready()) break;
					String password = bufferedReader.readLine();
					String password_hash = getPasswordHash(password);
					hashDictionary.put(password_hash, password);
				} catch (IOException e) {
                    throw new RuntimeException(e);
                }
            }
            try {
                bufferedReader.close();
				reader.close();
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        }
	/**
	 * Do the dictionary attack.
	 */
	public void doDictionaryAttack() {
		// create the rainbow dictionary
		addToHashDictionary("SoftwareSystems/src/ss/week6/dictionaryattack/linuxwords");
		// load the passwords
        try {
            readPasswords("SoftwareSystems/test/ss/week6/LeakedPasswords.txt");
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
		for (String user : passwordMap.keySet()) {
			if (hashDictionary.containsKey(passwordMap.get(user))) {
				System.out.println(user + ": " + hashDictionary.get(passwordMap.get(user)));
			}
		}
    }
	public static void main(String[] args) {
		DictionaryAttack da = new DictionaryAttack();
		//da.doDictionaryAttack();
		// Brute force Alice
		try {
			da.readPasswords("SoftwareSystems/test/ss/week6/LeakedPasswords.txt");
		} catch (IOException e) {
			e.printStackTrace();
		}
		String victim = "alice";
		long startTime = System.currentTimeMillis();
		String password = da.bruteForce(victim);
		long stopTime = System.currentTimeMillis();
		System.out.println(victim + " has password " + password);
		System.out.println("It took " + (stopTime - startTime) + "ms to crack it with brute force.");
	}

	// For 6.6
	// it takes (52 + nr_special_char + 10)^4 - for just 4 characters and on average / 2
	// if it is only letters lowercase it takes 26 ^ 4 / 2 on average
	// for ascii: (93 ^ 4) / 2
	// For 6.7
	// The time grows exponentially as we add more and more characters to the password
	public String bruteForce(String userName) {
		// Range of ascii printable characters: 33 - 126
		// Note, I could do this more modular with recursive looping but nah.
		byte start_range = 97;
		byte stop_range = 122;
		byte[] password = new byte[4];
		for (byte i = start_range; i <= stop_range; i++) {
			password[0] = i;
			for (byte j = start_range; j <= stop_range; j++) {
				password[1] = j;
				for (byte k = start_range; k <= stop_range; k++) {
					password[2] = k;
					for (byte l = start_range; l <= stop_range; l++) {
						password[3] = l;
						System.out.println("Trying " + new String(password));
						if (getPasswordHash(new String(password)).equals(passwordMap.get(userName))) {
							return new String(password);
						}
					}
				}
			}
		}
		return null;
	}

}
