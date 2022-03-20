package test;
import main.Exercises;

import java.util.Arrays;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Random;

public class ExercisesTest {
    private static final Exercises exercises = new Exercises();
    private static final int N = 20;
    private static final int MAX_ELEM = 5*N;
    private static final int NUM_TEST_CASES = 5000;
    private static final String LOG_FILE_PATH = "src/test/test_logs.txt";
    private static File TEST_LOG_FILE = new File(LOG_FILE_PATH);


    public void testMemberOfUnsortedRandom() {
        int maxIterations = 100;
        int testCasesUntilFail = 0;
        for (int iter = 0; iter < maxIterations; iter++) {
            RandomTestingFramework rtf = new RandomTestingFramework(NUM_TEST_CASES);
            for (int i = 0; i < rtf.randomArrays.length; i++) {
                boolean oracleAnswer = testOracle(rtf.randomArrays[i], rtf.randomKeys[i]);
                if (oracleAnswer != exercises.memberOfUnsorted(rtf.randomArrays[i], rtf.randomKeys[i])) {
                    testCasesUntilFail += (i + 1);
                    break;
                }
            }
        }
        System.out.println("Average number of test cases until error found (random): " + testCasesUntilFail/maxIterations);
    }

    public void testMemberOfUnsortedPairwise() {
        int testCasesUntilFail = 0;
        PairwiseTestingFramework ptf = new PairwiseTestingFramework();
        int[] pairwiseTestCase = new int[N + 1];
        for (int i = 0; i < ptf.typicalValues.length; i++) { // set all elements to default
            pairwiseTestCase[i] = ptf.typicalValues[i][0];
        }
        outerLoop:
        for (int i = 0; i < ptf.typicalValues.length - 1; i++) {
            pairwiseTestCase[i] = ptf.typicalValues[i][1]; // set element i to non-default
            for (int j = i + 1; j < ptf.typicalValues.length; j++) {
                testCasesUntilFail++;

                pairwiseTestCase[j] = ptf.typicalValues[j][1]; // set element j to non-default
                int[] array = Arrays.copyOfRange(pairwiseTestCase, 0, N);
                boolean oracleAnswer = testOracle(array, pairwiseTestCase[N]);
                ptf.writeTestCaseToFile(pairwiseTestCase, j);
                if (oracleAnswer != exercises.memberOfUnsorted(array, pairwiseTestCase[N]))
                    break outerLoop;
                pairwiseTestCase[j] = ptf.typicalValues[j][0]; // set element j back to default
            }
            pairwiseTestCase[i] = ptf.typicalValues[i][0]; // set element i back to default
        }
        System.out.println("Number of test cases until error found (pairwise): " + testCasesUntilFail);
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
                this.randomArrays[i] = randomArray(N);
            }
            this.randomKeys = randomArray(numTestCases);
            writeTestCasesToFile();
        }

        private static int[] randomArray(int length) {
            int[] array = new int[length];
            for (int i = 0; i < length; i++) {
                array[i] = random.nextInt(MAX_ELEM);
            }
            return array;
        }

        private void writeTestCasesToFile() {
            try {
                FileWriter writer = new FileWriter(TEST_LOG_FILE);
                for (int i = 0; i < randomArrays.length; i++) {
                    writer.write("\nRandom test case: " + (i+1) + "\n[");
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

    private class PairwiseTestingFramework {
        private int[][] typicalValues;
        private static final int k = 2;

        // Typical_1 = [0,1], Typical_2 = [5,6], Typical_3 = [10,11] etc.
        // Default_i = Typical_i[0]
        // Typical_N+1 = [1, 95] are the typical values for the key.
        private PairwiseTestingFramework() {
            typicalValues = new int[N+1][k];
            for (int i = 0; i < N; i++) {
                typicalValues[i][0] = 5*i;
                typicalValues[i][1] = 5*i + 1;
            }
            typicalValues[N] = new int[]{1,MAX_ELEM-5};
        }

        private void writeTestCaseToFile(int[] testCase, int number) {
            try {
                FileWriter writer = new FileWriter(TEST_LOG_FILE, true);
                writer.write("\nPairwise test case: " + number + "\n[");
                for (int i = 0; i < testCase.length-1; i++) {
                        if (i % 10 == 0)
                            writer.write("\n");
                        writer.write(testCase[i] + " ");
                    }
                    writer.write("\n]\n");
                    writer.write("KEY: " + testCase[testCase.length-1] +"\n");
                writer.close();
            } catch (IOException e) {
                System.err.println(e.getMessage());
            }
        }
    }

    public static void main(String[] args) {
        ExercisesTest t = new ExercisesTest();
        t.testMemberOfUnsortedRandom();
        t.testMemberOfUnsortedPairwise();
    }

    }
