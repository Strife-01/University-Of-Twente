package ss.week2;

import org.junit.jupiter.api.BeforeEach;
import ss.week2.p2_3_to_8.LampSetting;
import ss.week2.p2_3_to_8.ThreeWayLamp;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class ThreeWayLampTest {
    private ThreeWayLamp lamp;

    @BeforeEach
    public void init() {
        lamp = new ThreeWayLamp();
    }

    @Test
    public void testInitialLampState() {
        assertEquals(this.lamp.getCurrentLampState(), LampSetting.OFF);
    }

    @Test
    public void testLampSwitchSequence() {
        assertEquals(this.lamp.getCurrentLampState(), LampSetting.OFF);
        lamp.setNextSetting();
        assertEquals(this.lamp.getCurrentLampState(), LampSetting.LOW);
        lamp.setNextSetting();
        assertEquals(this.lamp.getCurrentLampState(), LampSetting.MEDIUM);
        lamp.setNextSetting();
        assertEquals(this.lamp.getCurrentLampState(), LampSetting.HIGH);
        lamp.setNextSetting();
        assertEquals(this.lamp.getCurrentLampState(), LampSetting.OFF);
    }

    @Test
    public void testOFF() {
        lamp.setLampOFF();
        assertEquals(this.lamp.getCurrentLampState(), LampSetting.OFF);
    }

    @Test
    public void testLOW() {
        lamp.setLampLOW();
        assertEquals(this.lamp.getCurrentLampState(), LampSetting.LOW);
    }

    @Test
    public void testMEDIUM() {
        lamp.setLampMEDIUM();
        assertEquals(this.lamp.getCurrentLampState(), LampSetting.MEDIUM);
    }

    @Test
    public void testHIGH() {
        lamp.setLampHIGH();
        assertEquals(this.lamp.getCurrentLampState(), LampSetting.HIGH);
    }

    @Test
    public void testMessage() {
        assertEquals("Current setting: OFF.", this.lamp.getCurrentLampState().getDescription());
    }
}
