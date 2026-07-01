import java.util.ArrayList;
import java.util.List;

public class Beremeles {
    record Employee(int years, boolean raisedLastYear, double salary) {
    }

    public static void main(String[] args) {
        List<Employee> employees = List.of(
                new Employee(20, false, 1234),
                new Employee(9, false, 423),
                new Employee(11, false, 34),
                new Employee(12, true, 134)
        );

        var list1 = findAtLeast10Years(employees);
        var list2 = findNotRaise(list1);
        double result = sumRaise(list2);
        System.out.println(result);

        double result2 = 0.0;
        for (var e : employees) {
            if (e.years >= 10) {
                if (!e.raisedLastYear) {
                    result2 += e.salary * 0.1;
                }
            }
        }
        System.out.println(result2);

        double result3 = 0.0;
        for (var e : employees) {
            if (e.years >= 10 && !e.raisedLastYear) {
                result3 += e.salary * 0.1;
            }
        }
        System.out.println(result3);

        double result4 = employees.stream()
                .filter(Beremeles::isHereLongEnough)
                .filter(Beremeles::notRecivedRaiseYet)
                .mapToDouble(Beremeles::calcRaise)
                .sum();
        System.out.println(result4);
    }

    private static boolean isHereLongEnough(Employee e) {
        System.out.println("long? "+e);
        return e.years() >= 10;
    }

    private static boolean notRecivedRaiseYet(Employee e) {
        System.out.println("not? "+e);
        return !e.raisedLastYear;
    }


    private static List<Employee> findAtLeast10Years(List<Employee> e) {
        List<Employee> r = new ArrayList<>();
        for (var emp : e) {
            if (emp.years >= 10) {
                r.add(emp);
            }
        }
        return r;
    }

    private static List<Employee> findNotRaise(List<Employee> e) {
        List<Employee> r = new ArrayList<>();
        for (var emp : e) {
            if (!emp.raisedLastYear) {
                r.add(emp);
            }
        }
        return r;
    }

    private static double sumRaise(List<Employee> e) {
        double result = 0.0;
        for (var emp : e) {
            result += calcRaise(emp);
        }
        return result;
    }

    private static double calcRaise(Employee e) {
        return e.salary * 0.1;
    }
}
