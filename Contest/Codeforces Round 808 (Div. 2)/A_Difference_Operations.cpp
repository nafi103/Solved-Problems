#include <bits/stdc++.h>
using namespace std;
 void solution()
{
    int n, flag = 1;
    cin >> n;
    int arr[n];
    for (int i = 0; i < n; i++)
        cin >> arr[i];
    for (int i = 1; i < n; i++)
    {
        if (arr[i] % arr[0] != 0)
            flag = 0;
    }
    if (flag == 1)
        cout << "Yes" << endl;
    else
        cout << "No" << endl;
}
 int main()
{
    int t;
    cin >> t;
    while (t--)
        solution();
}