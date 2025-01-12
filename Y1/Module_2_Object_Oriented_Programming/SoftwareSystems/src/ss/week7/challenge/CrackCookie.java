package ss.week7.challenge;

import org.apache.commons.codec.binary.Base64;

public class CrackCookie {
    public static void main(String[] args) {
        BadCookieCrypto badCookieCrypto = new BadCookieCrypto();
        String cypherText = badCookieCrypto.createCookie();
        byte[] rawData = Base64.decodeBase64(cypherText);
        System.out.println(new String(rawData));
    }
}
