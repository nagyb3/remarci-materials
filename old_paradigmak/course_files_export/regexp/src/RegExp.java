import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class RegExp {
    public static void main(String[] args) {
        String str = "alma (fa) van a kertben 523 km-en keresztül";
        Pattern p = Pattern.compile(".*?(\\d+).*");
        Matcher m = p.matcher(str);
        if(m.matches()) {
            String group1 = m.group(1);
            System.out.println(group1);
        } else {
            System.out.println("No match");
        }
        System.out.println("\u1F60B");
        System.out.println(Character.toChars(0x1F60B));
    }
}
