#include <../src/tapeins/sp24/physical/Streaming/src/Streaming.h>

void setup() {
 // put your setup code here, to run once:
 Serial.begin(115200);
}

void loop() {
 // put your main code here, to run repeatedly:
 Serial << "Current millis: " << millis() << " " << analogRead(A1)<< endl;
 delay(100);
}
