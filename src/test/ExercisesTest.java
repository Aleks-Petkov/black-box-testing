package test;
import static org.junit.Assert.assertEquals;
import org.junit.Test;
import main.Exercises;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Random;

public class ExercisesTest {
    private static final Exercises exercises = new Exercises();
    private static final int N = 20;
    private static final int MAX_ELEM = 100;
    private static final int NUM_TEST_CASES = 4;
    private static final String LOG_FILE_PATH = "src/test/test_logs.txt";
    private static File TEST_LOG_FILE = new File(LOG_FILE_PATH);
    private RandomTestingFramework rtf = new RandomTestingFramework(NUM_TEST_CASES);


    @Test
    public void testBinarySearch() {
        for (int i = 0; i < rtf.randomArrays.length; i++) {
            boolean oracleAnswer = testOracle(rtf.randomArrays[i], rtf.randomKeys[i]);
            System.out.println(oracleAnswer);
            assertEquals(oracleAnswer, exercises.memberOfUnsorted(rtf.randomArrays[i], rtf.randomKeys[i]));
        }
    }

    // Return true if key is a member of array and false otherwise.
    private boolean testOracle(int[] array, int key) {
        for (int i = 0; i < array.length; i++) {
            if (array[i] == key)
                return true;
        }
        return false;
    }
    private class RandomTestingFramework {
        private int[][] randomArrays;
        private int[] randomKeys;
        private static final Random random = new Random();

        private RandomTestingFramework(int numTestCases) {
            this.randomArrays = new int[numTestCases][N];
            for (int i = 0; i < numTestCases; i++) {
                this.randomArrays[i] = randomArray();
            }
            this.randomKeys = randomArray();
            writeTestCasesToFile();
        }

        private static int[] randomArray() {
            int[] array = new int[N];
            for (int i = 0; i < N; i++) {
                array[i] = random.nextInt(MAX_ELEM);
            }
            return array;
        }

        private void writeTestCasesToFile() {
            try {
                FileWriter writer = new FileWriter(TEST_LOG_FILE);
                for (int i = 0; i < randomArrays.length; i++) {
                    writer.write("\nTest case: " + (i+1) + "\n[");
                    for (int j = 0; j < randomArrays[i].length; j++) {
                        if (j % 10 == 0)
                            writer.write("\n");
                        writer.write(randomArrays[i][j] + " ");
                    }
                    writer.write("\n]\n");
                    writer.write("KEY: " + randomKeys[i] +"\n");
                }
                writer.close();
            } catch (IOException e) {
                System.err.println(e.getMessage());
            }
        }
    }

}
