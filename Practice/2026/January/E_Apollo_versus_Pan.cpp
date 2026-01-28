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

const int N = 5e5 + 10;
int a[N], cnt[60];

int expo(int a, int b){
    int res = 1;
    while(b > 0){
        if(b & 1)
            res = (res * a) % mod;
        a = (a * a) % mod;
        b >>= 1;
    }
    return res;
}

void solve()
{
    int n, ans = 0;
    cin >> n;
    memset(cnt, 0, sizeof cnt);
    for(int i = 0; i < n; i++){
        cin >> a[i];
        for(int j = 0; j < 60; j++){
            if(a[i] & (1ll << j))
                cnt[j]++;
        }
    }
    for(int j = 0; j < n; j++){
        int and_sum = 0, or_sum = 0;
        for(int i = 0; i < 60; i++){
            int p = expo(2, i);
            if(a[j] & (1ll << i)){
                or_sum = (or_sum + p * n) % mod;
                and_sum = (and_sum + p * cnt[i]) % mod;
            }else{
                or_sum = (or_sum + p * cnt[i]) % mod;
            }
        }
        ans = (ans + and_sum * or_sum) % mod;
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