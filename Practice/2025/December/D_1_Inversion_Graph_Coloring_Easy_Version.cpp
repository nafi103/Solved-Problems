#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 1e9 + 7;
const int inf = 1e18 + 10;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

const int N = 305;
int n, a[N], dp[N][N][N], power_of_two[N];

void input(){
    cin >> n;
    for(int i = 0; i < n; i++)
        cin >> a[i];
    for(int i = 0; i < n; i++){
        for(int j = 0; j <= n; j++){
            for(int k = 0; k <= n; k++)
                dp[i][j][k] = -1;
        }
    }
}

int f(int i, int j, int k){
    if(i == n)
        return 0;
    int &ans = dp[i][j][k];
    if(ans != -1)
        return ans;
    ans = f(i + 1, j, k);
    if(a[i] >= j)
        ans = (ans + f(i + 1, a[i], k)) % mod;
    else if(a[i] >= k)
        ans = (ans + f(i + 1, j, a[i])) % mod;
    else
        ans = (ans + power_of_two[n - 1 - i]) % mod;
    return ans;
}

void solve()
{
    input();
    cout << (power_of_two[n] - f(0, 0, 0) + mod) % mod << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    power_of_two[0] = 1;
    for(int i = 1; i < N; i++)
        power_of_two[i] = (power_of_two[i - 1] * 2) % mod;
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}