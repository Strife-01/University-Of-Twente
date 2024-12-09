package ss.week3;

public interface PayCalculator {
    static public int pay(int hourlyWage, int nrOfWorkedHours) {
        return hourlyWage * nrOfWorkedHours;
    }
}
