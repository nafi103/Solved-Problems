#include <bits/stdc++.h>
#define ll long long
using namespace std;

int main()
{
    int t;
    cin >> t;
    while (t--)
    {
        ll r, c;
        cin >> r >> c;
        if (r == 1 && c == 1)
            cout << 1 << endl;
        else if (r > c)
        {
            if (r % 2 == 0)
                cout << r * r - c + 1 << endl;
            else
                cout << (r - 1) * (r - 1) + c << endl;
        }
        else
        {
            if (c % 2 == 1)
                cout << c * c - r + 1 << endl;
            else
                cout << (c - 1) * (c - 1) + r << endl;
        }
    }
}