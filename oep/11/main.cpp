#include <iostream>

#include "system.h"

using namespace std;

int main()
{
    System sys(5);
    sys.writeState();

    cout << "arriving and getting out\n";
    sys._doors[0]->send(open);
    sys.writeState();

    cout << "closing the door\n";
    sys._doors[0]->send(close);
    sys.writeState();

    cout << "children are getting out\n";
    sys._doors[2]->send(open);
    sys.writeState();

    cout << "switching on the alarm system\n";
    sys._alarm->send(on);
    sys.writeState();

    cout << "closing the door\n";
    sys._doors[2]->send(close);
    sys.writeState();

    cout << "switching on the alarm system\n";
    sys._alarm->send(on);
    sys.writeState();

    cout << "somebody is moving in the car\n";
    sys._alarm->send(movement);
    sys.writeState();

    cout << "openning the door and catching the thief\n";
    sys._doors[0]->send(open);
    sys.writeState();

    cout << "switching off the alarm system\n";
    sys._alarm->send(off);
    sys.writeState();

    cout << "closing the door\n";
    sys._doors[0]->send(close);
    sys.writeState();

    cout << "switching on the alarm system\n";
    sys._alarm->send(on);
    sys.writeState();

    return 0;
}
