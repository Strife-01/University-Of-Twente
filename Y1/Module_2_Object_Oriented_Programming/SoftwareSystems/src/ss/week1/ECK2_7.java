package ss.week1;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Scanner;

public class ECK2_7 {
    public static void main(String[] args) {
        try {
            File file = new File("testdata.txt"); // Use the direct filename
            Scanner sc = new Scanner(file);

            // Read the first line as the student's name
            if (sc.hasNextLine()) {
                String studentName = sc.nextLine();
                System.out.println("Student Name: " + studentName);
            }

            float totalGrade = 0f;
            int nrOfCourses = 0;

            // Read the grades from each line
            while (sc.hasNextLine()) {
                String line = sc.nextLine();
                try {
                    float grade = Float.parseFloat(line); // Parse each line as a float
                    totalGrade += grade;
                    nrOfCourses++;
                } catch (NumberFormatException e) {
                    System.out.println("Invalid grade format: " + line);
                }
            }

            sc.close();
            System.out.println("Total Grade: " + totalGrade);
            System.out.println("Number of Courses: " + nrOfCourses);
            System.out.println("Average grade: " + totalGrade / (float) nrOfCourses);
        } catch (FileNotFoundException e) {
            System.out.println("File not found: " + e.getMessage());
        }
    }
}
