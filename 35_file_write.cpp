#include <iostream>
#include <fstream>
using namespace std;

int main() {
    ofstream outFile("output.txt");
    if (outFile.is_open()) {
        outFile << "Hello, this is written to a file.\n";
        outFile << "This is the second line.\n";
        outFile.close();
        cout << "Data written to file successfully." << endl;
    } else {
        cout << "Unable to open file" << endl;
    }
    return 0;
}
