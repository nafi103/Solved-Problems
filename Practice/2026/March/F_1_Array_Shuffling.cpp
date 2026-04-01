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
vector<vector<int>> save(N);
int cnt[N];

void solve()
{
    int n;
    cin >> n;
    for(int i = 1; i <= n; i++){
        save[i].clear();
        cnt[i] = 0;
    }
    vector<int> a(n), b(n);
    int mx = 0;
    for(int i = 0; i < n; i++){
        cin >> a[i];
        cnt[a[i]]++;
        mx = max(mx, cnt[a[i]]);
    }
    b = a;
    sort(all(b));
    for(int i = 0; i < n; i++){
        save[b[i]].push_back(b[(i + mx) % n]);
    }
    for(int i = 0; i < n; i++){
        cout << save[a[i]].back() << " \n"[i == n - 1];
        save[a[i]].pop_back();
    }
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