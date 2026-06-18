#include <bits/stdc++.h>
using namespace std;
 int main()
{
    int t;
    cin >> t;
    while (t--)
    {
        int n;
        cin >> n;
        int m = (n / 2) + (n % 2);
        int n1 = 1, n2 = n*3;
        cout << m << endl;
        if (n == 1)
            cout << "1 2" << endl;
        else
        {
            while (n1 < n2)
            {
                cout << n1 << " " << n2 << endl;
                n1 += 3;
                n2 -= 3;
            }
        }
    }
}