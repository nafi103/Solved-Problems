#include <bits/stdc++.h>

using namespace std;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

void solve()
{
    int n, r, m, rem;
    cin >> n >> r >> m;
    rem = n;
    vector<vector<int>> g(n+1);
    while(r--){
    	int u,v;
    	cin >> u >> v;
    	g[u].push_back(v);
    	g[v].push_back(u);
    }
    bool flag = true;
    vector<int> cover(n+1, -1);
    queue<array<int,3>> q;
    while(m--){
    	int k,s;
    	cin >> k >> s;
    	if(cover[k] != -1){
    		flag = false;
    	}
    	cover[k] = k;
    	q.push({k,k,s});
    }
    while(!q.empty() and flag){
    	auto [node, guard, rem_s] = q.front();
    	q.pop();
    	rem--;
    	if(rem_s == 0)
    		continue;
    	for(auto &adj: g[node]){ 
    		if(cover[adj] != guard){
    			if(cover[adj] != -1){
    				flag = false;
    				break;
    			}
    			cover[adj] = guard;
    			q.push({adj, guard, rem_s - 1});
    		}
    	}
    }
    if(flag and rem == 0)
    	cout << "Yes" << endl;
   	else
   		cout << "No" << endl;
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