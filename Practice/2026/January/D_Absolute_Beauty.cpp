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
int a[N], b[N], n;

void input(){
    cin >> n;
    for(int i = 1; i <= n; i++)
        cin >> a[i];
    for(int i = 1; i <= n; i++){
        cin >> b[i];
        if(a[i] > b[i])
            swap(a[i], b[i]);
    }
}

void solve()
{
    input();
    int ans = 0;
    for(int i = 1; i <= n; i++)
        ans += (b[i] - a[i]);
    int minb = inf, maxa = -inf;
    for(int i = 1; i <= n; i++){
        if(b[i] < minb)
            minb = b[i];
        if(a[i] > maxa)
            maxa = a[i];
    }
    ans += 2 * max(0ll, maxa - minb);
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