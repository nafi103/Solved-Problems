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

const int N = 2e5 + 10;
int fact_p2[N];

void solve()
{
    int n, ans = 0, x;
    cin >> n;
    for(int i = 0; i < n; i++){
        cin >> x;
        if(fact_p2[n - 1] - fact_p2[i] - fact_p2[n - i - 1] == 0)
            ans = (ans ^ x);
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

    for(int i = 2; i < N; i *= 2){
        for(int j = i; j < N; j += i)
            fact_p2[j]++;
    }
    for(int i = 2; i < N; i++)
        fact_p2[i] += fact_p2[i - 1];

    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}