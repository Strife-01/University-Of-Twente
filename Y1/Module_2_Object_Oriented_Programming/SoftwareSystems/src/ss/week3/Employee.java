package ss.week3;

public class Employee {
    private PayCalculator payCalculator;
    private int nrOfWorkedHours;
    private int hourlyWage;

    public Employee(PayCalculator payCalculator, int hourlyWage) {
        this.payCalculator = payCalculator;
        this.nrOfWorkedHours = 0;
        this.hourlyWage = hourlyWage;
    }

    /**
     * Returns the number of hours this Employee worked
     * in the current period.
     */
    public int hours () {
        return this.nrOfWorkedHours;
    }

    /**
     * Returns this Employee 's pay for the period.
     */
    public int pay () {
        if (hours() > 40) {
            return RegularPay.pay(this.hourlyWage, 40) + OvertimeWage.pay(hours() - 40, this.hourlyWage);
        }
        return RegularPay.pay(this.hourlyWage, hours());
    }
}
