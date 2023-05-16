static volatile int input_data[8] = {0,1,2,3,4,5,6,7};
static volatile int flag = 0;
static volatile int acc_thread0 = 0;

char *s = "Success\n";
char *f = "Failure\n";

void program_thread0(){
    for (int i = 0; i < 4; i++)
        acc_thread0 += input_data[i];
    char *p;


    while (flag == 0); // Wait until thread1 produced the value
    if (flag + acc_thread0 == 28) {
        for (p = s; p < s + 8; p++) putchar(*p);
    } else {
        for (p = f; p < f + 8; p++) putchar(*p);
    }
}


void program_thread1(){
    int a = 0;
     for (int i = 0; i < 4; i++)
        a += input_data[4+i];
    flag = a;
    while(1);
}


int main(int a){
    if (a == 0) {
        program_thread0();
    } else
    {
        program_thread1();
    }
}
