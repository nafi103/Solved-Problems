#include <bits/stdc++.h>
#define ll long long
using namespace std;

int main()
{
    int n;
    cin >> n;
    int arr[n];
    if (n == 1)
        cout << 1;
    else if (n == 2 || n == 3)
        cout << "NO SOLUTION";
    else
    {
        arr[n / 2] = n;
        arr[n / 2 + 1] = 2;
        arr[n / 2 - 1] = 1;
        for (int i = n / 2 + 2; i < n; i++)
        {
            arr[i] = arr[i - 1] + 2;
        }
        for (int i = n / 2 - 2; i >= 0; i--)
        {
            arr[i] = arr[i + 1] + 2;
        }
        for (int i = 0; i < n; i++)
        {
            cout << arr[i] << " ";
        }
    }
    cout<<endl;
}