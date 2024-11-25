/* ACM project Last Revised September 15th 2000 by Pezhman Boussina
This program is designed to work with SSRL designed ACM chassis.
The microcontroller used in this project is TERN design which 
uses AMDE188ES processor.
*/

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <dos.h>			
#include "ae.h"				// A_Engine initialization 
#include "aeee.h"

#define PPICMD 0x3			// PPI 0 (U16) command register for LCD
#define PPI0 0x0			// PPI 0 port 0
#define PPI1 0x1			// PPI 0 port 1
#define PPI2 0x2			// PPI 0 port 2

#define CS_80M 0x200   		// Address of digitizer
#define K 400				// duration of integration for beam (K*12.5ns)
#define N 400				// duration of integration for housekeeping (N*12.5ns)
#define V 10					// Number of running average
#define VP 20
#define BEG 10				// Starting point for integration
#define FACTOR 1.0			// Software FACTOR for calculation of beam current changed the factor from 2.098 to 1.88 to 3.56 to .993
#define SFault 450          // Software level for super fault
#define PPICMD2 0x103		// PPI 1 (U5) command register for parallel port
#define PPI10 0x100			// PPI 1 port 0
#define PPI11 0x101			// PPI 1 port 1
#define PPI12 0x102			// PPI 1 port 2
#define WAIT(n) {int i;\
for(i=0;i<(n);i++);}


unsigned char store[V][K];		// Two dimensional array for storing digitized values from the FIFO
unsigned long wave[V];			// One dimensional array for integrating beam individual waveforms
unsigned long dispwave[VP];		// New One dimensional array for integrating beam used in display and DAC
char buf2[24];					// Buffers used for ouputting text and values to LCD


unsigned int i;					// Variable for integrating the individual waveforms
unsigned int l;					// Variable for summing individual waveforms
unsigned int LA;				// Variable for summing individual waveforms
unsigned int j;					// Variable for performing Modulo operation based on 8 running averages
char datastore1[8];				// Array for storing the trip point for beam 
int trig;                       // Variable for storing the trigger value global
unsigned long dat1;  			// Variable for Storing beam trip point from the onboard A to D 
double beamTrip=0.0;			// Variable used for converting the beam trip level to floating point

long int fault,timer=0,timer2=0,timer1=0;		// Variables for timer operation to calculate frequency
unsigned int t,t0,t1,ta,tb,tm;					// Variables for setting up timer operation
unsigned long t0_int;								// Variable for the timer counter

void interrupt far t0_isr (void);           // Subroutine for calculating the frequency
void ppi_lcd_init(void);                    // Subroutine for initializing hantronix lcd
void ppi_lcdcmd(int cmd);                   // Subroutine to send commands to U5 for LCD
void ppi_lcddat(int dat);                   // Subroutine to send CHARACTERs to U5 for LCD
void ppi_lprintf(char* str);                // Subroutine to send data to U5 for LCD
void Acminit(void);                         // Initializing all the declared variables

void main(void)
{

	unsigned char entered=1;			// Variable to detect entrance into the trippoint adjust loop
	unsigned long allwave=0;			// Variable for summation of beam 8 (V) waves on a running average bases
	unsigned long allwave2=0;			// Variable for summation of beam 20 waves on a running average bases
	unsigned long house=0;			// Variable for integration of wave for housekeeping
	volatile int gain=50;				// Variable to store value of gain (External Pre_amp) base on switch setting
	int page=0;										// Variable to store LCD page to be displayed
	char ledd=0;										// Variable to use for blinking the LCD

	volatile int btrip=0;				// Variable to latch the beam trip value for LCD display until reset is pressed
	volatile int htrip=0;				// Variable to latch the house trip value for LCD display until reset is pressed
	volatile int strip=0;				// Variable to latch the super charge trip value for LCD display until reset is pressed

	int heart=0;					// Variable for LCD display purpose to show heartbeat from side to side
	double hkavg=0.0;					// Variable used for housekeeping conversion to floating point
	double beamavg=0.0;					// Variable used for beam average conversion to floating point
	double beamavgDisp=0.0;
	double freq=0.0;					// Variable used for storing frequency based on timers
	double flevel=0.0;					// Variable used for storing the value that tripped the beam
	double hkfault=0.0;					// Variable used for storing the value that tripped the housekeeping
	double scharge=0.0;					// Variable used for storing each integration for supercharge checks
	double slevel=0.0;					// Variable used for storing the Supercharge value if happened
	double hkTrip=0.0;				// Variable used for storing the house keeping trip point based on the gain settings
	int fpbeam=0;						// Variable used for ouputing the beam value using the D/A to front panel
	int remtrip=0;					// Variable used for ouputing the trip value of the beam using D/A to remote

	unsigned int loop=0;			// Counter for purpose of diplaying every (V) times
	char buf1[24];					// Buffers used for ouputting text and values to LCD
	char buf3[24];					// Buffers used for ouputting text and values to LCD
	char buf4[24];					// Buffers used for ouputting text and values to LCD
	char buf5[24];					// Buffers used for ouputting text and values to LCD
	char buf6[24];					// Buffers used for ouputting text and values to LCD
	char buf7[24];					// Buffers used for ouputting text and values to LCD
	union bits{
		struct bitsforuse{
			volatile unsigned int trigger:1;
			volatile unsigned int times:1;
			volatile unsigned int tripSet:1;
			volatile unsigned int pageSelect:1;
			volatile unsigned int tripreset:1;
			volatile unsigned int testtrip:1;
			volatile unsigned int NotUsed1:1;	
			volatile unsigned int NotUsed2:1;
		}tern;
		volatile unsigned char dummy;
	}ten;// declaring a structure for reading toggled bits
	ae_init();									// Initialization routines for TERN
	Acminit();									// Initialization for ACM variables
	while(1)
	{
		ten.dummy=inportb(PPI10);					// Read PPI line of tern 
		// Check for SRS trigger
		trig=ten.tern.trigger;
		if(ten.tern.trigger==1)						// If there is trigger continue if not fall back into the while loop
			continue;
		page=ten.tern.pageSelect;
		//while( 0x01&inportb(CS_80M+0xb0) ); 	// Wait for FIFO to fill, this will continue till fifo fills up
		while(inportb(0xff74)&0x40);
		l=j%V;									// Modulo operation for doing the running average.
		LA=j%VP;
		wave[l]=0;								// Sets the value of the integrated waveform being replaced to 0
		dispwave[LA]=0;
		for(i=0;i<BEG;i++)						// Store all the points till BEG in the array ( will not be used)
		{
			store[l][i]=inportb(CS_80M+0xc0);	// Command used to read fifo and store the data in store array
		}
		for(i=BEG;i<K;i++)						// Store the waveform in store array and integrate using wave array
		{
			store[l][i]=inportb(CS_80M+0xc0);	// Command used to read fifo and store the data in store array
			wave[l]=wave[l]+store[l][i];		// integrate the current pulse
			dispwave[LA]=dispwave[LA]+store[l][i];
		}
		j++;									// increment the j variable for the next pulse
		allwave=0;								// Set the variable allwave to 0 to sum up current set of pulses
		allwave2=0;
		for(l=0;l<V;l++)						// using the for loop to sum up the last set of pulses 
		{
			allwave=allwave+wave[l];
		}
		for(LA=0;LA<VP;LA++)						// using the for loop to sum up the last set of pulses 
		{
			allwave2=allwave2+dispwave[LA];
		}
		if(ten.tern.times==0)						// Check the gain setting switch in the ACM chassis (PRE_AMP defined)
		{
			gain=50;							// Gain value based on the switch position
			hkTrip=2.0; 						// House keeping trip point based on the switch position
		}
		else
		{
			gain=50;						
			hkTrip=2.0;					
		}
		beamavg=0;		
		beamavgDisp=0.0;// Clear the previous valued of beamavg
		beamavg=(allwave/((K-BEG) * 255.0 * V));	// Calculate the beamavg based on an 8 bit A to D
		beamavgDisp=(allwave2/((K-BEG) * 255.0 * VP));	// Calculate the beamavgDisp based on an 8 bit A to D
		beamavg=(beamavg*12.5*(K-BEG))/(FACTOR*gain);	// Used 2.098 FACTOR to calculate beam current 
		beamavgDisp=(beamavgDisp*12.5*(K-BEG))/(FACTOR*gain);	// Used 2.098 FACTOR to calculate beam current 
		scharge=(wave[(j-1)%V]*12.5)/(255.0*FACTOR*gain);	// Calculate the beam current for latest pulse, supercharge check
		outportb(CS_80M+0xa0, 0);				// RESET FIFO low active
		outportb(CS_80M+0xa0, 1);				// RESET high
		//housekeeping 
		outportb(0x101,0x00);					// Send a pulse to U5 port1 bit 1
		WAIT(10);        						// Short pause
		outportb(0x101,0x01);					// Toggle the bit up
		WAIT(10);       						// Short pause
		outportb(0x101,0x00);					// Toggle the bit down
		while( 0x01&inportb(CS_80M+0xb0) ); 	// Wait for FIFO to fill /ff					
		house=0;								// Clear the last value of house keeping
		hkavg=0;								// Clear the last floating point value of house keeping
		for(i=0;i<BEG;i++)						// Throw away the points 0 to BEG
		{
			inportb(CS_80M+0xc0);				// Read the data but do not store (begining points)
		}
		for(i=BEG;i<N;i++)						// Read the data from beginning till nth point
		{
			house=house+inportb(CS_80M+0xc0);	// Grab the data and integrate
		}
		hkavg=(house/(255.0*(N-BEG)));			// Convert the house keeping value to floating point
		hkavg=hkavg*12.5*(N-BEG)/(FACTOR*gain); // Calculate the house keeping value based on gain,FACTOR,12.5 ns
		outportb(CS_80M+0xa0, 0);				// RESET FIFO low active
		outportb(CS_80M+0xa0, 1);				// RESET high
		if(hkavg>hkTrip && beamavg<beamTrip && scharge<SFault) 	// generate heart beat if there is no trip
		{
			outportb(0x101,0x00);								// Toggle U5 port 1 bit 2 to 0
			WAIT(10);       									// Wait
			outportb(0x101,0x02);								// Toggle U5 port 1 bit 2 to 1
			WAIT(10);											// Wait
			outportb(0x101,0x00);								// Toggle U5 port 1 bit 2 to 0
		} 
		if(ten.tern.tripreset==0)				// If the trip reset button is pushed reset the trips	and trip values
		{
			btrip=0;
			htrip=0;
			strip=0;
			flevel=0;
		}
		if(beamavg>=beamTrip && btrip==0)	// Store the value that tripped the beam in flevel and keep it until reset
		{
			btrip=1;
			flevel=(wave[(j-1)%V]/((K-BEG) * 255.0));
			flevel=flevel*12.5*(K-BEG)/(FACTOR*gain);
		}
		if(scharge>=SFault && strip==0)		// Store the valued that tripped the beam in slevel and keep it until reset
		{
			strip=1;
			slevel=scharge;
		}
		if(hkavg<hkTrip && htrip==0)		// Store the value that tripped the house in hkfault and keep it until reset
		{
			htrip=1;
			hkfault=hkavg;
		} 
		if(ten.tern.tripSet==0) 				// Fall in if the key for changing the trip point has been turned
		{
			entered=0;					
			ae_ad12(9); 					// Read the a to d number 9 
			dat1=0;
			for(i=0;i<10;i++)
			{
				dat1=dat1+ae_ad12(9);		// Take ten readings sum and average for less variations 
			}
			dat1=dat1/10;
			sprintf(datastore1,"%d",dat1);
			beamTrip=(double)dat1;			// Convert the reading to floating point based on 12 bits and 4.096 volts
			beamTrip= beamTrip*.001220703*100.0;
		}
		if(entered==0 && ten.tern.tripSet==1)	// Enter this loop only if the key is turned to set the value into the memory
		{
			entered=1;
			outportb(0x102,0x01 | inportb(0x102));
			pio_init(11, 0);				// Set P11 output low
			for(i=0;i<8;i++)
			{
				ee_wr(i,datastore1[i]); 	// Write the value of the beam trip point into the EEPROM
			}
			pio_init(11, 1);				// Set P11 output pulled high
		}
		timer1=t0_int;						//*65535;
		timer=timer1-timer2;
		t0_int=0;
		timer2=t0_int;						//*65535; 
		ledd = ~ledd;						// Convert the timer data into floating point frequency
		freq=(double)(1000.0/timer);
		fpbeam=(int)(beamavgDisp*100);			// Use the D/A to place on the front panel spiggot the beam average value
		remtrip=(int)(flevel*100);			// Use the D/A to place the value faulting the system on rear output	
		ae_da(remtrip,fpbeam);
		if((loop%5)==1) 					// Display every vth time
		{	
			led(ledd); 						// Blink the LED
			if(page==1) 					//page 1
			{
				ppi_lcdcmd(0x01);
				ppi_lcdcmd(0x02); 
				sprintf(buf1,"BEAM  = %3.2f nA",beamavgDisp);
				ppi_lcdcmd(0x80);
				ppi_lprintf(buf1);
				ppi_lcdcmd(0x80);
				ppi_lprintf(buf1);
				if(btrip==1)
				{
					sprintf(buf2,"BEAM FAULT %3.2f nA",flevel);
					ppi_lcdcmd(0xA0);
					ppi_lprintf(buf2);
					
				}
				if(strip==1)
				{
					sprintf(buf2,"SUPER FAULT %3.2f nA",slevel);
					ppi_lcdcmd(0xA0);
					ppi_lprintf(buf2);
					
				}
				if(strip==0 && btrip==0)
				{
					sprintf(buf2,"FREQ  = %3.1f Hz",freq);
					ppi_lcdcmd(0xA0);
					ppi_lprintf(buf2);
				}
				sprintf(buf3,"BEAM TP  = %3.2f nA",beamTrip);
				ppi_lcdcmd(0xC0);
				ppi_lprintf(buf3);
				if(heart==0)
				{
					sprintf(buf4,"%c%c%c",31,31,31);
					heart=1;
				}
				else
				{
					sprintf(buf4,"       %c%c%c",30,30,30);
					heart=0;
				}
				ppi_lcdcmd(0xE0);
				ppi_lprintf(buf4);
			}	  
			if(page==0) 						//page 2
			{
				ppi_lcdcmd(0x01);
				ppi_lcdcmd(0x02); 
				sprintf(buf5,"HOUSE KP = %3.2f nA",hkavg);
				ppi_lcdcmd(0x80);
				ppi_lprintf(buf5);
				sprintf(buf6,"HOUSE TP = %3.2f nA",hkTrip);
				ppi_lcdcmd(0xA0);
				ppi_lprintf(buf6);
				if(htrip==0)
					sprintf(buf7,"Gain     =  %3d",gain);
				if(htrip==1)
					sprintf(buf7,"HK FAULT  %3.2fnA",hkfault);
				ppi_lcdcmd(0xC0);
				ppi_lprintf(buf7); 
				if(heart==0)
				{
					sprintf(buf4,"%c%c%c",31,31,31);
					heart=1;
				}
				else
				{
					sprintf(buf4,"       %c%c%c",30,30,30);
					heart=0;
				}
				ppi_lcdcmd(0xE0);
				ppi_lprintf(buf4);		 
			}
		}
		loop++;	
	}
}
void Acminit(void)
{
	pio_init(6,1);                      // Set P6 for input to check for fifo full (new boards)
    pio_init(12, 2);					// Set P12 output 
    pio_init(26, 2);					// Set P26 output  
    pio_init(29, 2);					// Set P29 output  
    pio_init(11, 1);					// Set P11 input pulled high
    pio_init(18,0);						// P18=/CTS1=SCC2=PCS2 output   
    pio_init(14,3);						// Set p14 for input detection
    outportb(CS_80M+0xa0, 0);			// RESET FIFO low active
    outportb(CS_80M+0xa0, 1);			// RESET high
    outportb(CS_80M+0xb0, 0);			// PWD low, ADC active

    ta=10000;							// interrupt at 10000x0.1 us=1 ms 
    tb=10000;							// interrupt at 10000x0.1 us=1 ms 
    t0_int=0;							// for timer
    outportb(PPICMD,0x80);				// PPI U16, all output
    ppi_lcd_init();						// INITIALIZE HANTRONIX LCD
    outportb(0x103,0x90);				// PPI U5 PORT 0 INPUT 1 AND 2 OUTPUT
    tm = 0xe003;		//start timer0, ALT max A and B, int. enabled   
    t0_init(tm,ta,tb,t0_isr);   
    outportb(0x102,0x01 | inportb(0x102));
    pio_init(11, 0);						// Set P11 input pulled high
    for(i=0;i<8;i++)						// read in the value of EEPROM for the beam trip point level set
    {
		datastore1[i]=ee_rd(i);
	}
    dat1=atoi(datastore1);					// Convert the data from the EEPROM
    pio_init(11, 1);						// Set P11 input pulled high
    beamTrip=(double)dat1;
    beamTrip= beamTrip*.001220703*100;		// Calculate the trip point value
    for(j=0;j<V;j++)						// Clear the array used for calculating the trip points
    {
		for(i=0;i<K;i++)
		{
			store[j][i]=0;
		}
    }
    j=0; 
}
// LCD ROUTINES
// LINE 1 LEFT FIRST CHARACTER = 0X80
// LINE 2 LEFT FIRST CHARACTER = 0XA0
// LINE 3 LEFT FIRST CHARACTER = 0XC0
// LINE 4 LEFT FIRST CHARACTER = 0XE
// 0X1 clear the display and return to home position
// 0X2 return the cursor to home position
// 0X0b display on, cursor on, blink charachter at cursor position
 
void ppi_lcd_init(void)
{
    unsigned int m;
    outportb(PPICMD,0x80);			// all output
    outportb(PPI1,0);   
    outportb(PPI0, 0);
    outportb(PPI2,0);				// LCD=I27, R/W=I25, A0=I26 low
    for(m=0; m<3; m++)
    {
        ppi_lcdcmd(0x30);
        delay_ms(40);				// 4 ms delay
    }								// 3 times function set per hantronics
    ppi_lcdcmd(0x3b);				// function set 4 lines e0 and e1 high
									// otherwise dots appear as well as first
									// four letters of each line
    delay_ms(40);					// 4 ms delay
    ppi_lcdcmd(0x0c);				// 0X0c display on, cursor off, blink cursor position off
									// 0X0b display on, cursor on, cursor position off
									// 0X0f all on
    delay_ms(40);					// 4 ms delay
    ppi_lcdcmd(0x01);				// clear display
    delay_ms(40);                   // 4 ms delay
    ppi_lcdcmd(0x02);				//return to home position
    delay_ms(40);					// 4 ms delay
}
void ppi_lcdcmd(int cmd)
{ 
    outportb(PPI0,cmd);
    outportb(PPI2,inportb(PPI2)&0x1f);		// LCD=B27 /RW=B25 A0=B26 low
    outportb(PPI2,inportb(PPI2)|0x80);		// LCD high
    outportb(PPI2,inportb(PPI2)&0x1f);
	delay_ms(1);
}
void ppi_lcddat(int dat)
{ 
    outportb(PPI0,dat);
    outportb(PPI2,0x5f);					// A0=B26 high, LCD = B27, R/W = B25 low
    outportb(PPI2,inportb(PPI2)|0x80);		// LCD high
    outportb(PPI2,inportb(PPI2)&0x7f);		// LCD low
	delay_ms(1);
}  
void ppi_lprintf(char* str)
{
    char* p;
    int kp;
    p=str;
    for(kp=0;kp<strlen(str);kp++)
    {
        ppi_lcddat((unsigned char)*p);
        p++;    
    }
}
void    interrupt far t0_isr (void)
{
    t0_int++;
	if(((t0_int%1000)==0) && trig==1)
	{
		sprintf(buf2,"NO TRIGGER           ");
		ppi_lcdcmd(0xA0);
		ppi_lprintf(buf2);
	}
	if(((t0_int%1000)==0) && trig==0)
	{
		sprintf(buf2,"BUFFER NOT GETTING FULL");
		ppi_lcdcmd(0xA0);
		ppi_lprintf(buf2);
	}


	
	//  /* Issue EOI for the interrupt */
    outport(0xff22,0x8000);
//  outport(0xff22,0x0008);
}

