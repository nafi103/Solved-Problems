#include <bits/stdc++.h>
using namespace std;
 void solution()
{
    int n;
    cin >> n;
    int arr[n][n];
    int n1 = 1, n2 = n * n;
    for (int i = 0; i < n; i++)
    {
        if (i % 2 == 0)
        {
            for (int j = 0; j < n; j++)
            {
                if ((i + j) % 2 == 0)
                {
                    arr[i][j] = n1;
                    n1++;
                }
                else
                {
                    arr[i][j] = n2;
                    n2--;
                }
            }
        }
        else
        {
            for (int j = n - 1; j >= 0; j--)
            {
                if ((i + j) % 2 == 0)
                {
                    arr[i][j] = n1;
                    n1++;
                }
                else
                {
                    arr[i][j] = n2;
                    n2--;
                }
            }
        }
    }
    for (int i = 0; i < n; i++)
    {
        for (int j = 0; j < n-1; j++)
        {
            cout<<arr[i][j]<<" ";
        }
        cout<<arr[i][n-1]<<endl;
    }
}
 int main()
{
    int t;
    cin >> t;
    while (t--)
        solution();
}