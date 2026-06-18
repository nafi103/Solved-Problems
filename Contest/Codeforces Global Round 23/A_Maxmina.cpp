#include <bits/stdc++.h>
using namespace std;
 int main()
{
    int t;
    cin >> t;
    while (t--)
    {
        int n, k, sum = 0;
        cin >> n >> k;
        int arr[n];
        for (int i = 0; i < n; i++)
        {
            cin >> arr[i];
            sum += arr[i];
        }
        if (sum > 0)
            cout << "YES" << endl;
        else
            cout << "NO" << endl;
    }
}