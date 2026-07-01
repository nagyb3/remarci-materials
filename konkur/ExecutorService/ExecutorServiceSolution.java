import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.ThreadLocalRandom;
import java.util.concurrent.TimeUnit;

public class ExecutorServiceSolution {


    public static void main(String[] args) {
        withRunnable();
        withCallable();
    }

    public static int N_CLIENTS = 100_000;

    public static final /* note: final, an Object */ Object sumLoansLock = new Object();
    public static /* note: not final, not an Object */ int sumLoans = 0; // protected by `sumLoansLock`

    public static void withRunnable() {
        int[] clientLoans = new int[N_CLIENTS];

        ExecutorService exec = Executors.newFixedThreadPool(10);
        for (int i = 0; i < N_CLIENTS; i++) {

            final int ii = i;

            Runnable task = () -> {
                int loan = ThreadLocalRandom.current().nextInt(10);
                synchronized (clientLoans) {
                    clientLoans[ii] = loan;
                }
                synchronized (sumLoansLock) {
                    sumLoans += loan;
                }
            };

            exec.submit(task); // only a "task", not a thread; cf. `new Thread(task).start()` (too many threads)
        }

        exec.shutdown();
        try {
            exec.awaitTermination(10000, TimeUnit.DAYS);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
        System.out.println(sumLoans);
        System.out.println(Arrays.stream(clientLoans).sum());

        assert sumLoans == Arrays.stream(clientLoans).sum();
    }


    public static void withCallable() {
        sumLoans = 0;
        int[] clientLoans = new int[N_CLIENTS];
        List<Future<Integer>> clientLoansFutures = new ArrayList<>(N_CLIENTS); // note: pls. no array for Generic types
        ExecutorService exec = Executors.newFixedThreadPool(10);
        for (int i = 0; i < N_CLIENTS; i++) {

            Callable<Integer> task = () -> {
                int loan = ThreadLocalRandom.current().nextInt(10);
                synchronized (sumLoansLock) {
                    sumLoans += loan;
                }
                return loan;
            };

            clientLoansFutures.add(exec.submit(task)); // not the loan, but a "promise"
        }

        for (int i = 0; i < N_CLIENTS; i++) {
            Future<Integer> loanFuture = clientLoansFutures.get(i);
            try {
                clientLoans[i] = loanFuture.get(); // wait until this loan is available ...
            } catch (InterruptedException | ExecutionException e) { // ... or an exception is thrown
                throw new RuntimeException(e);
            }
        }

        exec.shutdown();
        try {
            exec.awaitTermination(10000, TimeUnit.DAYS);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }

        System.out.println(sumLoans);
        System.out.println(Arrays.stream(clientLoans).sum());

        assert sumLoans == Arrays.stream(clientLoans).sum();
    }
}
