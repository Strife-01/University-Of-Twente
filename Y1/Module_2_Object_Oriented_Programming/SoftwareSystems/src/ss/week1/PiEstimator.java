package ss.week1;

import java.util.Scanner;
import java.lang.Math;

public class PiEstimator {
    /**
     * If we take a circle of radius 1, and we compute the area we get PI
     * If we take a square around it we get area 4
     * If we restrict ourselves in the first quadrant we get aread of circl squarted = pi/4 and area
     * for square 1
     * Now if we pick a random point in the small square, the chance of being on the circle part is
     * pi/4 / 1 = pi/4 so we can approximate the pi by randomly choosing points in the square and
     * if they are in the circle we increment n. By doing this we get the approximation probability
     * of a random point to be in the circle aka pi/4. Multiply by 4 and we get the pi approx
     */
    public static void main(String[] args) {
        Scanner sc = new Scanner(System.in);
        System.out.print("Please enter the number of iterations: ");
        long N = sc.nextInt();
        double n = 0; // Lucky iterations
        double xCoord;
        double yCoord;
        // Approximate pi
        for (int i = 0; i < N; i++) {
            xCoord = Math.random();
            yCoord = Math.random();
            if (xCoord * xCoord + yCoord * yCoord <= 1.0) {
                n++;
            }
        }
        double pi = (n/(double)N) * 4.0;
        System.out.println("The pi is " + pi);
    }
}
