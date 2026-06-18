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

const int N = 5e5 + 10;
int fact[N];

struct Segment_Tree{
	vector<int> st, v;

	Segment_Tree(vector<int> _v){
		v = _v;
		int n = sz(v) - 1;
		st.resize(4 * n);
		build(1,1,n);
	}

	void build(int node, int b, int e){
		if(b == e){
			st[node] = v[b];
			return;
		}
		int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
		build(left, b, mid);
		build(right, mid + 1, e);
		st[node] = (st[left] + st[right]) % mod;
	}

	void update(int node, int b, int e, int id, int val){
		if(b == e){
			st[node] = val;
			v[b] = val;
			return;
		}
		int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
		if(id <= mid)
			update(left, b, mid, id, val);
		else
			update(right, mid + 1, e, id, val);
		st[node] = (st[left] + st[right]) % mod;
	}

	int query(int node, int b, int e, int &l, int &r){
		if(e < l or b > r)
			return 0;
		if(b >= l and e <= r)
			return st[node];
		int mid = (b + e) / 2, left = 2 * node, right = 2 * node + 1;
		return (query(left, b, mid, l, r) + query(right, mid + 1, e, l, r)) % mod;
	}
};

map <int, int> other = {
	{3628800, 821984089},
	{39916800, 644056242},
	{479001600, 527656359}
};

struct DSU{
	int n;
	vector<int> p, v;
	vector<bool> zero;

	DSU(int _n, vector<int> _v){
		n = _n;
		zero.assign(n + 2, false);
		p.resize(n + 2); v = _v;
		v.push_back(inf);
		p[n + 1] = n + 1;
		for(int i = n; i >= 1; i--){
			find(i);
		}
	}

	int find(int i){
		if(v[i] == 1 or v[i] == 2 or (v[i] == 0 and zero[i])){
			return p[i] = find(p[i + 1]);
		}
		return p[i] = i;
	}

	void update(int l, int r, Segment_Tree &st){
		for(int i = find(l); i <= r; i = find(i + 1)){
			int x;
			if(zero[i]){
				x = 0;
			}else if(v[i] > 12){
				zero[i] = true;
				if(v[i] < N){
					x = fact[v[i]];
				}else{
					x = other[v[i]];
				}
			}else{
				zero[i] = false;
				x = fact[v[i]];
			}
			v[i] = x;
			st.update(1,1,n,i,x);
		}
	}
};

void solve() {
	int n, m;
	cin >> n >> m;
	vector<int> v(n + 1);
	for(int i = 1; i <= n; i++)
		cin >> v[i];
	Segment_Tree st(v);
	DSU uf(n, v);
	while(m--){
		int t;
		cin >> t;
		if(t == 1){
			int l, r;
			cin >> l >> r;
			uf.update(l, r, st);
		}else{
			int l, r;
			cin >> l >> r;
			cout << st.query(1,1,n,l,r) << endl;
		}
	}
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);


    fact[0] = 1;
	for(int i = 1; i < N; i++) 
		fact[i] = (fact[i - 1] * i) % mod ;

    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}