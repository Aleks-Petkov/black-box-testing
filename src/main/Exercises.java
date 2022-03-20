package main;

import test.ExercisesTest;

import java.io.File;

import static org.junit.Assert.assertEquals;

public class Exercises {
    //@ requires v != null;
    //@ ensures (\forall int i; 0 <= i < v.length; v[i+1] > v[i]) &&
    //@         (\forall int i; 0 <= i && i < v.length;
    //@            (\num_of int j; 0 <= j && j < v.length;
    //@               v[i] == \old(v[j])) ==
    //@            (\num_of int j; 0 <= j && j < v.length;
    //@               v[i] == v[j])
    //@         );
    // The second 'ensures' condition is taken from: https://stackoverflow.com/questions/47994171/java-sort-method-in-jml
    // to ensure that the elements in the array are unchanged. More specifically, the number of occurrences of
    // an element v[i] in the unsorted array is the same as the number of occurrences of v[i] in the sorted array.
    public void insertionSort(int[] v) {
        for (int i = 1; i < v.length; i++){ // error 3: set i < v.length-1
            int j = i;
            while (j > 0 && v[j-1] > v[j]){
                int temp = v[j];
                v[j] = v[j-1];
                v[j-1] = temp;
                j--;
            }
        }
    }

    //@ requires v != null && (\exists int i; 0 <= i < v.length; v[i] == key);
    //@ ensures \result == i;
    //@ also
    //@ requires v != null && (\forall int i; 0 <= i < v.length; v[i] != key);
    //@ ensures \result == -1;
    public int search(int[] v, int key) {
        return 0; // Function not implemented
    }

    //@ requires v != null && (\exists int i; 0 <= i < v.length; v[i] == key) && (\forall int i; 0 <= i < v.length; v[i+1] > v[i]);
    //@ ensures \result == true;
    //@ also
    //@ requires v != null && (\forall int i; 0 <= i < v.length; v[i] != key) && (\forall int i; 0 <= i < v.length; v[i+1] > v[i]);
    //@ ensures \result == false;
    public boolean memberOfSorted(int[] v, int key) {
        return (binarySearch(v, key) != -1);
    }


    //@ requires v != null && (\exists int i; 0 <= i < v.length; v[i] == key);
    //@ ensures \result == true;
    //@ also
    //@ requires v != null && (\forall int i; 0 <= i < v.length; v[i] != key)
    //@ ensures \result == false;
    public boolean memberOfUnsorted(int[] v, int key) {
        insertionSort(v); // error 4: comment out this line
        return memberOfSorted(v, key); // error 6: set key = 0;
    }

    //@ requires v != null && (\exists int i; 0 <= i < v.length; v[i] == key) && (\forall int i; 0 <= i < v.length; v[i+1] > v[i]);
    //@ ensures \result == i;
    //@ also
    //@ requires v != null && (\forall int i; 0 <= i < v.length; v[i] != key) && (\forall int i; 0 <= i < v.length; v[i+1] > v[i]);
    //@ ensures \result == -1;
    public int binarySearch(int[] v, int key) {
        int mid;
        int lo = 0; // error 1: lo = 1
        int hi = v.length-1; // error 2: hi = v.length-2;
        do {
            mid = (lo + hi) / 2;

            if (key < v[mid])
                hi = mid -1 ;
            else
                lo = mid + 1;
        } while (key != v[mid] && lo <= hi); // error 5: set lo < hi

        if (key == v[mid])
            return mid;
        else
            return -1;
    }
}