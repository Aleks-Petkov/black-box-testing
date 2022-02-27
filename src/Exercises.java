public class Exercises {
    // 2. (i)
    //@ requires v != null;
    //@ ensures (\forall int i; 0 <= i < v.length; v[i+1] > v[i]);
    //@         (\forall int i; 0 <= i && i <= v.length;
    //@            (\num_of int j; 0 <= j && j <= v.length;
    //@               v[i] == \old(v[j])) ==
    //@            (\num_of int j; 0 <= j && j <= v.length;
    //@               v[i] == v[j])
    //@         );
    // The second 'ensures' condition is taken from: https://stackoverflow.com/questions/47994171/java-sort-method-in-jml
    // to ensure that the elements in the array are unchanged.

    // 3. (i)
    static public void insertionSort(int[] v) {
        for (int i = 1; i < v.length; i++){
            int j = i;
            while (j > 0 && v[j-1] > v[j]){
                int temp = v[j];
                v[j] = v[j-1];
                v[j-1] = temp;
                j--;
            }
        }
    }

    // 2. (ii)
    //@ requires v != null && (\exists int i; 0 <= i < v.length; v[i] == key);
    //@ ensures \result == i;
    //@ also
    //@ requires v != null && (\forall int i; 0 <= i < v.length; v[i] != key);
    //@ ensures \result == -1;
    static public int search(int[] v, int key) {return 0;}

    // 2. (iii)
    //@ requires v != null && (\exists int i; 0 <= i < v.length; v[i] == key);
    //@ ensures \result == true;
    //@ also
    //@ requires v != null && (\forall int i; 0 <= i < v.length; v[i] != key);
    //@ ensures \result == false;
    
    // 3. (ii)
    static public boolean memberOfSorted(int[] v, int key) {
        return (binarySearch(v, key) != -1);
    }

    // 2. (iii)
    //@ requires v != null && (\exists int i; 0 <= i < v.length; v[i] == key) && (\forall int i; 0 <= i < v.length; v[i+1] > v[i]);
    //@ ensures \result == true;
    //@ also
    //@ requires v != null && (\forall int i; 0 <= i < v.length; v[i] != key) && (\forall int i; 0 <= i < v.length; v[i+1] > v[i]);
    //@ ensures \result == false;

    // 3. (iii)
    static public boolean memberOfUnsorted(int[] v, int key) {
        insertionSort(v);
        return memberOfSorted(v, key);
    }

    // 2. (iv)
    //@ requires v != null && (\exists int i; 0 <= i < v.length; v[i] == key) && (\forall int i; 0 <= i < v.length; v[i+1] > v[i]);
    //@ ensures \result == i;
    //@ also
    //@ requires v != null && (\forall int i; 0 <= i < v.length; v[i] != key) && (\forall int i; 0 <= i < v.length; v[i+1] > v[i]);
    //@ ensures \result == -1;
    static public int binarySearch(int[] v, int key) {
        int mid;
        int lo = 1;
        int hi = v.length;
        do {
            mid = (lo + hi) / 2;
            if (key < v[mid]) 
                hi = mid -1 ;
            else
                lo = mid + 1;
        } while (key != v[mid] && lo <= hi);

        if (key == v[mid])
            return mid;
        else
            return -1;
    }
    public static void main(String[] args) {
        int[] v = new int[]{1, 3, 2, 5, 6, 4, 79, 32, 623, 5123, 1312};
        System.out.println(memberOfUnsorted(v, 1313));
    }
}