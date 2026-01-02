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

const int N = 5005;
int tn, n, arr[N], a[N], dp[N][N], suff[N];

void input(){
    n = 0;
    cin >> tn;
    for(int i = 0; i < tn; i++)
        cin >> arr[i];
    sort(arr , arr + tn);
    int last = arr[0], cnt = 1, mx = 1;
    for(int i = 1; i < tn; i++){
        if(arr[i] != last){
            last = arr[i];
            mx = max(mx, cnt);
            a[n] = cnt;
            cnt = 1, n++;
        }else{
            cnt++;
        }
    }
    for(int i = n - 1; i >= 0; i--){
        suff[i] = (i < n - 1 ? max(suff[i + 1] , a[i]) : a[i]);
    }
    mx = max(mx, cnt);
    a[n] = cnt;
    n++;
    for(int i = 0; i < n; i++){
        for(int j = 0; j <= mx; j++)
            dp[i][j] = -1;
    }
}

int f(int i, int j){
    if(i == n)
        return j == 0;
    int &ans = dp[i][j];
    if(ans != -1)
        return ans;
    ans = f(i + 1, max(j, a[i]));
    if(a[i] >= j)
        ans = (ans + (a[i] - j + 1) * f(i + 1, 0)) % mod;
    return ans;
}

void solve()
{
    input();
    cout << f(0, 0) << endl;
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