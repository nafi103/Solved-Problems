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

void solve()
{
    string str;
    cin >> str;
    reverse(all(str));
    int extra = str.back() - '0';
    str.pop_back();
    int ans = 0, sum = 0;
    sum += extra;
    for(auto &x: str)
        sum += (x - '0');
    sort(all(str));
    while(sum > 9){
        if(extra - 1 > (str.back() - '0')){
            sum -= (extra - 1);
            extra = 0;
        }
        else{
            sum -= (str.back() - '0');
            str.pop_back();
        }
        ans++;
    }
    cout << ans << endl;
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}