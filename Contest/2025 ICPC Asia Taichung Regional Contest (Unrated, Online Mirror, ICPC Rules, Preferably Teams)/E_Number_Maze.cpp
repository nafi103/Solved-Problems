#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

map<string, vector<string>> pre;

void solve()
{
    int x, y;
    string str;
    cin >> str >> x >> y;
    x--, y--;
    string a = pre[str][x], b = pre[str][y];
    x = 0, y = 0;
    for (int i = 0; i < sz(a); i++){
        if(a[i]==b[i])
            x++;
        else
            y++;
    }
    cout << x << "A" << y << "B" << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    vector<string> str = {"12", "123", "1234"};
    for(auto &x: str){
        int pos = 1;
        string tmp = x;
        do{
            pre[x].push_back(tmp);
        } while (next_permutation(all(tmp)));
    }
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}