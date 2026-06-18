#include <bits/stdc++.h>
using namespace std;
 void solution()
{
    int n;
    cin >> n;
    vector<int> v(n);
    for (int i = 0; i < n; i++)
    {
        cin >> v[i];
    }
    sort(v.begin(), v.end());
    if (v[0] != v[n - 1])
    {
        cout<<"YES"<<endl;
        cout << v[n - 1] << " " << v[0] << " ";
        for (int i = n - 2; i >= 1; i--)
        {
            cout << v[i] << " ";
        }
        cout << endl;
    }else cout<<"NO"<<endl;
}
 int main()
{
    int t;
    cin >> t;
    while (t--)
        solution();
}