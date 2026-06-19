#include <bits/stdc++.h>
using namespace std;
 void solution()
{
    int value = 1;
    string str;
    cin >> str;
    transform(str.begin(), str.end(), str.begin(), ::toupper);
    if (str == "YES")
        cout << "YES" << endl;
    else
        cout << "NO" << endl;
}
 int main()
{
    int t;
    cin >> t;
    while (t--)
        solution();
}
