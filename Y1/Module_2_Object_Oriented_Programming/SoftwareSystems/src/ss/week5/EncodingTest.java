package ss.week5;

import org.apache.commons.codec.Decoder;
import org.apache.commons.codec.DecoderException;
import org.apache.commons.codec.binary.Base64;
import org.apache.commons.codec.binary.BinaryCodec;
import org.apache.commons.codec.binary.Hex;

/**
 * A simple class that experiments with the Hex encoding
 * of the Apache Commons Codec library.
 *
 */
public class EncodingTest {
    public static void main(String[] args) throws DecoderException {
        String bytes = "4d6f64756c652032";
        String input = "Hello World";
        String secondInput = "Hello Big World";
        String base64 = new String(Base64.encodeBase64(input.getBytes()));

        System.out.println(Hex.encodeHexString(input.getBytes()));
        System.out.println(Hex.encodeHexString(secondInput.getBytes()));
        System.out.println(new String(Hex.decodeHex(bytes)));
        System.out.println(base64);
        System.out.println(new String(Base64.encodeBase64(Hex.decodeHex("010203040506"))));
        System.out.println(new String(Base64.decodeBase64("U29mdHdhcmUgU3lzdGVtcw==")));
        for (int i = 1; i <= 10; i++) {
            String toBeEncoded = "";
            for (int j = 0; j < i; j++) {
                toBeEncoded += "a";
            }
            System.out.println(new String(Base64.encodeBase64(toBeEncoded.getBytes())));
        }
    }
}
