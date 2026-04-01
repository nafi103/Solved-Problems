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
int ans[2 * N];
vector<bool>visited(N);

void solve()
{
    int n, k;
    cin >> n >> k;
    fill(visited.begin(), visited.begin() + n + 1, false);
    if(k < n or k >= 2 * n){
        cout << "NO" << endl;
        return;
    }
    cout << "YES" << endl;
    int waste = k - n;
    set<int> seen;
    if(waste){
        ans[0] = 2;
        ans[1] = 1;
        seen.insert(1);
        seen.insert(2);
        waste--;
    }else{
        ans[0] = ans[1] = 1;
        visited[1] = true;
    }
    int i = 2, p = 3, q = 1;
    for(i; waste > 0; i += 2, p++, q++, waste--){
        ans[i] = p; ans[i + 1] = q;
        if(seen.count(q)){
            seen.erase(q);
            visited[q] = true;
        }
        seen.insert(p);
    }
    for(i; !seen.empty(); i++){
        ans[i] = *seen.begin();
        visited[ans[i]] = true;
        seen.erase(seen.begin());
    }
    p = 1;
    while(p <= n and visited[p])
        p++;
    for(i; i < 2 * n; i += 2, p++){
        ans[i] = ans[i + 1] = p;
    }
    for(i = 0; i < 2 * n; i++)
        cout << ans[i] << (i == 2 * n - 1 ? '\n': ' ');
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