/*
 * Project myProject
 * Author: Your Name
 * Date:
 * For comprehensive documentation and examples, please visit:
 * https://docs.particle.io/firmware/best-practices/firmware-template/
 */

// Include Particle Device OS APIs
#include "Particle.h"

// Let Device OS manage the connection to the Particle Cloud
SYSTEM_MODE(AUTOMATIC);

// Run the application and system concurrently in separate threads
SYSTEM_THREAD(ENABLED);

// Show system, cloud connectivity, and application logs over USB
// View logs with CLI using 'particle serial monitor --follow'
SerialLogHandler logHandler(LOG_LEVEL_INFO);

int MICROPHONE_PIN = A0;
float val;

/*SS => A5 (D14) (but can use any available GPIO)
SCK => SCK (D13)
MISO => MISO (D11)
MOSI => MOSI (D12)*/

/*he user's code must control the slave-select pin with digitalWrite() before and after each SPI transfer for the desired SPI slave device. Calling SPI.end() does NOT reset the pin mode of the SPI pins.*/
int ss = A5;

// setup() runs once, when the device is first turned on
void setup()
{
  SPI.setBitOrder(order); // LSBFIRST (least-significant bit first) or MSBFIRST

  // SPI.setClockSpeed(value, scale);
  // SPI.setClockSpeed(frequency); //don't change system clock change clock divider?
  /*
  SPI_CLOCK_DIV2
  SPI_CLOCK_DIV4
  SPI_CLOCK_DIV8
  SPI_CLOCK_DIV16
  SPI_CLOCK_DIV32
  SPI_CLOCK_DIV64
  SPI_CLOCK_DIV128
  SPI_CLOCK_DIV256
  */
  SPI.setClockDivider(divider); //clock reference is 64 MHz.

  SPI.setDataMode(mode);

  // spi setup https://docs.particle.io/reference/device-os/api/spi/
  SPI.begin(SPI_MODE_MASTER, ss);



  SPI.transfer(); // 0x10002, 0x3000A, 0x50008 (setup crossbars)
}

void myFunction(uint8_t state) {
  // called when selected or deselected
  transfer();//transfer data to chip
} //this function is called when chip is selected

// loop() runs over and over again, as quickly as it can execute.
void loop()
{

  val = analogRead(MICROPHONE_PIN);
  
  SPI.onSelect(myFunction);//select chip

  
  

  Serial.print(val);



  //example code 
  /*
  digitalWrite(chipSelectPin, LOW);  // Select the slave device

    SPI.beginTransaction(spiSettings);  // Start the transaction

    byte data = SPI.transfer(0x55);  // Send and receive a byte

    Serial.print("Received data: ");
    Serial.println(data, HEX);  // Print the received byte in hexadecimal

    SPI.endTransaction();  // End the transaction

    digitalWrite(chipSelectPin, HIGH);  // Deselect the slave device

    delay(1000);  // Wait 1 second before sending again
  */
}
