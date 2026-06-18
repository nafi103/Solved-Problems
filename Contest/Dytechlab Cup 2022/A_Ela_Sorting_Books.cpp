#include <bits/stdc++.h>
#define ll long long
using namespace std;
 void solution()
{
    vector<char>v;
    ll n, k;
    char c;
    string str;
    cin >> n >> k >> str;
    if (k == 0||n==0)
    {
        cout << endl;
    }
    else
    {
        ll arr[400] = {0}, div = n / k;
        for (int i = 0; i < n; i++)
        {
            arr[(int)str[i] - 96]++;
        }
        arr[div + 1] = 0;
        for (int i = 1; i <= k; i++)
        {
            bool flag = 0;
            for (int i = 1; i <= div + 1; i++)
            {
                if (arr[i] <= 0 && flag == 0)
                {
                    c = (int)(96 + i);
                    flag = 1;
                    continue;
                }
                arr[i]--;
            }
            v.push_back(c);
        }
        for (int i = 0; i < v.size(); i++)
        {
            cout<<v[i];
        }
        cout<<endl;
    }
}
 int main()
{
    int t;
    cin >> t;
    while (t--)
        solution();
    return 0;
}