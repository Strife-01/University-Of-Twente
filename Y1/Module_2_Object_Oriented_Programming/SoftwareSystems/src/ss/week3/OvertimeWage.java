package ss.week3;

public class OvertimeWage implements PayCalculator {
    private static final double OVERTIME_RATE_INCREASE = 1.5;

    static public int pay(int hourlyWage, int nrOfOvertimeHours) {
        return (int) (hourlyWage * nrOfOvertimeHours * OVERTIME_RATE_INCREASE);
    }
}
