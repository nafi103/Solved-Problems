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

const int N = 3e3 + 2;
int dp[N][N], arr[N], n, m;
vector<vector<int>> divisors(N);

void input(){
    cin >> n >> m;
    for(int i = 0; i < n; i++){
        cin >> arr[i];
        for(int j = 1; j <= m; j++)
            dp[i][j] = -1;
    }
}

int f(int i, int curr){
    if(curr > m)
        return 0;
    if(i == n - 1){
        if(arr[i] == 0)
            return 1;
        else
            return curr == arr[i];
    }
    int &ans = dp[i][curr];
    if(ans != -1)
        return ans;
    ans = 0;
    if(arr[i] != 0 and arr[i] != curr)
        return 0;
    for(auto &d: divisors[curr]){
        ans = (ans + f(i + 1, curr + d)) % mod;
    }
    return ans;
}

void solve()
{
    input();
    cout << f(0, 1) << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    for(int i = 1; i < N; i++){
        for(int j = i; j < N; j += i)
            divisors[j].push_back(i);
    }
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}