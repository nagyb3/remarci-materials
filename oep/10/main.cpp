#include <iostream>
#include <cassert>

#include "owen.h"

using namespace std;

/*
Azoknak az állapotgépeknek (magnetron, lámpa) van eseménysora, amelyek több irányból kaphatnak üzeneteket.
A többi állapotgép (gomb, ajtó) szinkron metódus-hívásokra reagál.
*/

int main()
{
    Owen owen;
    owen.writeState();

    cout << "Door is openning\n";
    owen._door->open();
    owen.writeState();

    cout << "Door is closing\n";
    owen._door->close();
    owen.writeState();

    cout << "Button is pressing\n";
    owen._button->press();
    owen.writeState();

    cout << "Button is pressing\n";
    owen._button->press();
    owen.writeState();

    cout << "Door is openning\n";
    owen._door->open();
    owen.writeState();

    cout << "Door is closing\n";
    owen._door->close();
    owen.writeState();

    return 0;
}

