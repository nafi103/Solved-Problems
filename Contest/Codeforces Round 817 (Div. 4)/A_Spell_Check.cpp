#include <bits/stdc++.h>
using namespace std;
 void solution()
{
    int n, cnt = 0,arr[5]= {0},value=1;
    string s;
    cin >> n;
    cin >> s;
    for (int i = 0; i < n; i++)
    {
        if(s[i] == 'T') arr[0]++;
        else if(s[i] == 'i') arr[1]++;
        else if(s[i] == 'm') arr[2]++;
        else if(s[i] == 'u') arr[3]++;
        else if(s[i] == 'r') arr[4]++;
    }
    for(int i = 0; i < 5; i++){
        if(arr[i] != 1) {
            value = 0; 
            break;
        }
    }
    if (value == 1 && n ==5)
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