#include <bits/stdc++.h>
using namespace std;
 void solution()
{
    int n, arr[4], flag = 0;
    cin>>n;
    arr[0] = 0;
    for (int i = 1; i < 4; i++)
        cin >> arr[i];
    if (arr[n] != 0)
    {
        if (arr[arr[n]] != 0)
        {
            flag = 1;
        }
    }
    if (flag == 1)
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