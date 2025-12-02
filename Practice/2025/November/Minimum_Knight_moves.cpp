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

int dist[8][8][8][8];
int dx[] = { -2, -1, 1, 2, -2, -1, 1, 2 };
int dy[] = { -1, -2, -2, -1, 1, 2, 2, 1 };

bool valid(int &r, int &c){
	return r >= 0 and r < 8 and c >= 0 and c < 8;
}

void solve()
{
    string a, b;
    cin >> a >> b;
    int sr = a[0] - 'a', sc = a[1] - '1', dr = b[0] - 'a', dc = b[1] - '1';
    if(dist[sr][sc][dr][dc] != -1){
    	cout << dist[sr][sc][dr][dc] << endl;
    	return;
    }
    dist[sr][sc][sr][sc] = 0;
    queue<array<int, 3>> q;
    q.push({sr, sc, 0});
    while(!q.empty()){
    	auto [cr, cc, d] = q.front();
    	q.pop();
    	for(int i = 0; i < 8; i++){
    		int ar = cr + dx[i], ac = cc + dy[i];
    		if(valid(ar,ac) and dist[sr][sc][ar][ac] == -1){
    			dist[sr][sc][ar][ac] = d + 1;
    			q.push({ar, ac, d + 1});
    		}
    	}
    }
    cout << dist[sr][sc][dr][dc] << endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    memset(dist, -1, sizeof dist);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}