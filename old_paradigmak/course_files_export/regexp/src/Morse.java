import java.util.HashMap;
import java.util.Map;

public class Morse {
    private static Map<String, String> toMorse = new HashMap<>();
    private static Map<String, String> toAlpahbet = new HashMap<>();

    private static void map(String alpabet, String morse) {
        toMorse.put(alpabet, morse);
        toAlpahbet.put(morse, alpabet);
    }

    static {
        map("A", " .- ");
        map("B", " -.. ");
        map("C", " -.-. ");
    }

    public static void main(String[] args) {
        String str1 = "ABC";
        String str2 = "ABBA";

        System.out.println(convertToMorse(str1));
        System.out.println(convertToMorse(str2));

        String str3 = " .-  -..  -.-. ";
        String str4 = " .-  -..  -..  .- ";

        System.out.println(convertToAlphabet(str3));
        System.out.println(convertToAlphabet(str4));

    }

    private static String convertToMorse(String text) {
        String current = text;
        for(var e: toMorse.entrySet()) {
            current = current.replace(e.getKey(), e.getValue());
        }
        return current;
    }

    private static String convertToAlphabet(String text) {
        String current = text;
        for(var e: toAlpahbet.entrySet()) {
            current = current.replace(e.getKey(), e.getValue());
        }
        return current;
    }
}
