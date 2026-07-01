import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Set;

public class Feladatok {
    public static void main(String[] args) throws IOException {
        PrintWriter pw2;
        try (PrintWriter pw = new PrintWriter("out.txt")) {
            String fix = "kosar ";
            Files.lines(Path.of("input.txt"))
                    .skip(3)
                    .filter(s->s.length()>5)
                    .map(s -> fix + s)
                    .limit(2)
                    .sorted(Comparator.comparingInt(Feladatok::countDifferentLetters).reversed())
                    .map(Feladatok::toPalindrom)
                    .forEach(pw::println);
        }
    }

    private static int countDifferentLetters(String line) {
        Set<Character> counter = new HashSet<>();
        for(int i=0; i<line.length(); ++i) {
            counter.add(line.charAt(i));
        }
        return counter.size();
    }

    private static String toPalindrom(String s) {
        if(isPalindrom(s)) {
            return s;
        }
        StringBuilder sb = new StringBuilder();
        sb.append(s);
        String reversed = sb.reverse().toString();
        return s+reversed;
    }

    private static boolean isPalindrom(String s) {
        for(int i=0, j = s.length()-1; i<j; ++i, --j) {
            if(s.charAt(i) != s.charAt(j)) {
                return false;
            }
        }
        return true;
    }
}
