package ss.week3;

public class RegularPay implements PayCalculator {
    static public int pay(int hourlyWage, int nrOfWorkedHours) {
        return hourlyWage * nrOfWorkedHours;
    }
}
