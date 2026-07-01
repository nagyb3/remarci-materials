import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;

public class Feladat3 {

    private static String ignoreCase = "AS";

    public static void main(String[] args) throws Exception {
        List<String> replace = ignoreCase.chars().mapToObj(b->new String(new byte[]{(byte)b})).toList();
        List<String> lines1 = Files.readAllLines(Path.of("file1.txt"));
        List<String> lines2 = Files.readAllLines(Path.of("file2.txt"));
        for(int i=0; i<lines1.size() && i<lines2.size(); ++i) {
            String str1 = toLowerCase(lines1.get(i), replace);
            String str2 = toLowerCase(lines2.get(i), replace);
            if(str1.equals(str2)) {
                System.out.println(i);
            }
        }
    }

    private static String toLowerCase(String input, List<String> toReplace) {
        String current = input;
        for(String s: toReplace) {
            current = current.replace(s, s.toLowerCase(Locale.ROOT));
        }
        return current;
    }

}
