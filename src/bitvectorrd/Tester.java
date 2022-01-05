package bitvectorrd;
import java.util.Scanner;

public class Tester {

	/**
	 * @param args
	 */
	public static void foo1(boolean input){
		int a, b, c;
		a = 42;
		b = 87;
		if(input){
			c = a + b;
		}
		else{
			c = a - b;
		}
	}

	public static void foo2(){
		int v, w, x, y, z;
		x = 5;
		y = -x;
		z = x + y;
		v = x * y;
		w = x / y;
	}

	public static void foo3(){
		int p, q, r;
		int arr[] = new int[10];
		p = -2;
		q = -5;
		p = p * p;
		r = arr[p];
		if(r > 0){
			q = q * q;
		}
		else{
			q = q + q;
		}
	}

	public static int foo4(int input){
		int i, res;
		res = 1;
		for(i = 2; i <= input; i++){
			res = res * i;
		}
		return(res);
	}
	
	public static void foo5(){
		int a = 0;
		int b = 5;
		int c = -5;
		int d = a * b;
		int e = d / b;
		b += a;
		c += a;
	}
}
