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

const int N = 3e5 + 10;
int dp[N][101], n;
bool inc[N];
string str;

int f(int i, int rem){
    if(rem == 0){
        return 0;
    }
    if(rem > 100 or i >= n - 2)
        return inf;

    int &ans = dp[i][rem];
    if(ans != -1)
        return ans;

    if(inc[i])
        ans = f(i + 3, rem);
    else
        ans = min(f(i + 1, rem), ((str[i] != 'A') + (str[i + 1] != 'B') + (str[i + 2] != 'C')) + f(i + 3, rem - 1 + inc[i] + inc[i + 1] + inc[i + 2]));
    return ans;
}

void solve()
{
    int k;
    cin >> str >> k;
    n = sz(str);
    for(int i = 0; i < n; i++){
        for(int j = 0; j < 101; j++){
            dp[i][j] = -1;
        }
    }

    for(int i = 0; i < n; i++){
        inc[i] = 0;
    }
    for(int i = 0; i + 2 < n; i++){
        if(str[i] == 'A' and str[i + 1] == 'B' and str[i + 2] == 'C'){
            inc[i] = true;
        }
    }

    int ans = f(0, k);

    if(ans == inf)
        cout << -1 << endl;
    else
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