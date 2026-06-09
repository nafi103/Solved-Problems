#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

void calc(int x, int d, set<int> &s){
    int nd = x / d;
    if((d + nd) % 4 != 0)
        return;
    int m = (d + nd) / 4;
    if(m < 0)
        return;
    if((d - 2 * m - 1) % 2 != 0)
        return;
    int n = (d - 2 * m - 1) / 2;
    s.insert(n);
}

void solve()
{
    int n;
    cin >> n;
    set<int> s;
    int newN = 4 * n - 1;
    for(int i = 1; i * i <= abs(newN); i++){
        if(newN % i == 0){
            calc(newN, i, s);
            calc(newN, -i, s);
            calc(newN, newN/ i, s);
            calc(newN, -newN / i, s);
        }
    }
    cout << sz(s) << endl;
    for(auto &x: s)
        cout << x << " ";
    cout << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}