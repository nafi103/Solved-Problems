#include <bits/stdc++.h>
using namespace std;
 void solution()
{
    int n, arr[26] = {0},cnt = 0;
    cin >> n;
    char Carr[n];
    for (int i = 0; i < n; i++)
    {
        cin >> Carr[i];
        if (arr[Carr[i] - 65] == 0)
            arr[Carr[i] - 65] += 2;
        else
            arr[Carr[i] - 65] ++;
    }
    for (int i = 0; i < 26; i++)   cnt+= arr[i];
    cout<< cnt<<endl; 
}
 int main()
{
    int t;
    cin >> t;
    while (t--)
        solution();
}