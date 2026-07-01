import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Feladat1 {
    public static void main(String[] args) {
        String task = "Delete (this) and (this also) from the text";
        Pattern pattern = Pattern.compile("\\([^)]+\\)");
        //Pattern pattern = Pattern.compile("\\(.*?\\)");
        Matcher m = pattern.matcher(task);
        if (m.find()) {
            System.out.println(m.replaceAll(""));
        }

    }
}
