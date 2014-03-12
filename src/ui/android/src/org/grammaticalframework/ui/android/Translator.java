package org.grammaticalframework.ui.android;

import android.content.Context;
import android.content.SharedPreferences;
import android.content.res.XmlResourceParser;
import android.text.TextUtils;
import android.util.Log;
import android.view.inputmethod.CompletionInfo;

import org.grammaticalframework.pgf.Concr;
import org.grammaticalframework.pgf.Expr;
import org.grammaticalframework.pgf.FullFormEntry;
import org.grammaticalframework.pgf.MorphoAnalysis;
import org.grammaticalframework.pgf.PGF;
import org.grammaticalframework.pgf.ParseError;
import org.xmlpull.v1.XmlPullParserException;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;

public class Translator {

    private static final String TAG = "Translator";

    /*

    // old

    // TODO: allow changing
    private String mGrammar = "ParseEngAbs.pgf";

    // TODO: build dynamically?
    private Language[] mLanguages = {
	    new Language("en-US", "English", "ParseEng", R.xml.qwerty),
        new Language("bg-BG", "Bulgarian", "ParseBul", R.xml.cyrillic),
        new Language("cmn-Hans-CN", "Chinese", "ParseChi", R.xml.qwerty),   
        new Language("fr-FR", "French", "ParseFre", R.xml.qwerty),  
        new Language("de-DE", "German", "ParseGer", R.xml.qwerty), 
        new Language("hi-IN", "Hindi", "ParseHin", R.xml.devanagari_page1, R.xml.devanagari_page2), 
        new Language("sv-SE", "Swedish", "ParseSwe", R.xml.qwerty), 
        new Language("fi-FI", "Finnish", "ParseFin", R.xml.qwerty),
    };
     */

    // /*
    // new

    // TODO: allow changing
    private String mGrammar = "App.pgf" ;

    // TODO: build dynamically?
    private Language[] mLanguages = {
	new Language("en-US", "English", "AppEng", R.xml.qwerty),
	new Language("cmn-Hans-CN", "Chinese", "AppChi", R.xml.qwerty),   
        new Language("sv-SE", "Swedish", "AppSwe", R.xml.qwerty), 
        new Language("fi-FI", "Finnish", "AppFin", R.xml.qwerty),
    };
    // */

    private Context mContext;

	private GrammarLoader mGrammarLoader;
    private ConcrLoader mSourceLoader;
    private ConcrLoader mTargetLoader;
    private ConcrLoader mOtherLoader;

	private static final String SOURCE_LANG_KEY = "source_lang";
	private static final String TARGET_LANG_KEY = "target_lang";
	
	private SharedPreferences mSharedPref;
	
	private Language getPrefLang(String key, int def) {
		int index = mSharedPref.getInt(key, def);
		if (index < 0 || index >= mLanguages.length)
			index = def;
		return mLanguages[index];
	}

	private void setPrefLang(String key, Language def) {
		for (int index = 0; index < mLanguages.length; index++) {
			if (def == mLanguages[index]) {
				SharedPreferences.Editor editor = mSharedPref.edit();
				editor.putInt(key, index);
				editor.commit();
				break;
			}
		}
	}

    public Translator(Context context) {
    	mContext = context;

		mSharedPref = context.getSharedPreferences(
				context.getString(R.string.global_preferences_key), Context.MODE_PRIVATE);

		mGrammarLoader = new GrammarLoader();
		mGrammarLoader.start();
		
		Language prefSourceLang = getPrefLang(SOURCE_LANG_KEY, 0);
		Language prefTargetLang = getPrefLang(TARGET_LANG_KEY, 1);
		
        mSourceLoader = new ConcrLoader(prefSourceLang);
        mSourceLoader.start();
        
        if (prefSourceLang == prefTargetLang) {
        	mTargetLoader = mSourceLoader;
        } else {
        	mTargetLoader = new ConcrLoader(prefTargetLang);
        	mTargetLoader.start();
        }

        mOtherLoader = null;
    }

    public List<Language> getAvailableLanguages() {
        return Arrays.asList(mLanguages);
    }

    public Language getSourceLanguage() {
        return mSourceLoader.getLanguage();
    }

    public void setSourceLanguage(Language language) {
    	setPrefLang(SOURCE_LANG_KEY, language);

    	if (mSourceLoader.getLanguage() == language)
    		return;
    	if (mTargetLoader.getLanguage() == language) {
    		cacheOrUnloadLanguage(mSourceLoader);
    		mSourceLoader = mTargetLoader;
    		return;
    	}
    	if (mOtherLoader != null &&
    	    mOtherLoader.getLanguage() == language) {
    		ConcrLoader tmp = mSourceLoader;
    		mSourceLoader = mOtherLoader;
    		mOtherLoader  = tmp;
    		return;
    	}

    	try {
    		mSourceLoader.join();
		} catch (InterruptedException e) {
			Log.e(TAG, "Loading interrupted", e);
		}

    	if (mSourceLoader.getLanguage() != mTargetLoader.getLanguage()) {
    		cacheOrUnloadLanguage(mSourceLoader);
    	}

        mSourceLoader = new ConcrLoader(language);
        mSourceLoader.start();
    }

    public boolean isSourceLanguageLoaded() {
    	try {
    		mSourceLoader.join();
    		return true;
		} catch (InterruptedException e) {
			Log.e(TAG, "Loading interrupted", e);
		}
    	return false;
    }

    private Concr getSourceConcr() {
    	try {
    		mSourceLoader.join();
		} catch (InterruptedException e) {
			Log.e(TAG, "Loading interrupted", e);
		}
        return mSourceLoader.getConcr();
    }

    public Language getTargetLanguage() {
        return mTargetLoader.getLanguage();
    }

    public void setTargetLanguage(Language language) {
    	setPrefLang(TARGET_LANG_KEY, language);

    	if (mTargetLoader.getLanguage() == language)
    		return;
    	if (mSourceLoader.getLanguage() == language) {
    		cacheOrUnloadLanguage(mTargetLoader);
    		mTargetLoader = mSourceLoader;
    		return;
    	}
    	if (mOtherLoader != null &&
    	    mOtherLoader.getLanguage() == language) {
    		ConcrLoader tmp = mTargetLoader;
    		mTargetLoader = mOtherLoader;
    		mOtherLoader  = tmp;
    		return;
    	}

    	try {
    		mTargetLoader.join();
		} catch (InterruptedException e) {
			Log.e(TAG, "Loading interrupted", e);
		}

    	if (mSourceLoader.getLanguage() != mTargetLoader.getLanguage()) {
    		cacheOrUnloadLanguage(mTargetLoader);
    	}

    	mTargetLoader = new ConcrLoader(language);
    	mTargetLoader.start();
    }

    public boolean isTargetLanguageLoaded() {
    	try {
    		mTargetLoader.join();
    		return true;
		} catch (InterruptedException e) {
			Log.e(TAG, "Loading interrupted", e);
		}
    	return false;
    }

    private Concr getTargetConcr() {
    	try {
    		mTargetLoader.join();
		} catch (InterruptedException e) {
			Log.e(TAG, "Loading interrupted", e);
		}
        return mTargetLoader.getConcr();
    }

	private void cacheOrUnloadLanguage(ConcrLoader loader) {
		if (mOtherLoader != null) {
			mOtherLoader.getConcr().unload();
			Log.d(TAG, mOtherLoader.getLanguage().getConcrete() + ".pgf_c unloaded");
		}
		mOtherLoader = loader;
	}

    public void switchLanguages() {
    	ConcrLoader tmp = mSourceLoader;
    	mSourceLoader = mTargetLoader;
    	mTargetLoader = tmp;
    }

    private static String explode(String in) {
    	String out = "";
    	for (int i = 0; i < in.length(); i++) {
    		if (i > 0)
    			out += ' ';
    		out += in.charAt(i);
    	}
    	return out;
    }
    /**
     * Takes a lot of time. Must not be called on the main thread.
     */
    public String translate(String input) {
        if (getSourceLanguage().getLangCode().equals("cmn-Hans-CN")) {
        	// for Chinese we need to put space after every character
        	input = explode(input);
        }

        try {
            Concr sourceLang = getSourceConcr();
	    Expr expr = sourceLang.parseBest(getGrammar().getStartCat(), input);
            Concr targetLang = getTargetConcr();
            String output = targetLang.linearize(expr);
            return output;
        } catch (ParseError e) {
            Log.e(TAG, "Parse error: " + e);
            return "parse error: " + e.getMessage();
        }
    }

    public String generateLexiconEntry(String lemma) {
        Concr sourceLang = getSourceConcr();
        Concr targetLang = getTargetConcr();
    	String cat = getGrammar().getFunctionType(lemma).getCategory();
		
    	Expr e1 = Expr.readExpr(lemma);
    	Expr e2 = Expr.readExpr("MkTag (Inflection"+cat+" "+lemma+")");

    	if (targetLang.hasLinearization("Inflection"+cat)) {
	        if (targetLang.hasLinearization(lemma))
	        	return sourceLang.linearize(e1) + " - " + targetLang.linearize(e2) + ". " + targetLang.linearize(e1);
	        else
	        	return sourceLang.linearize(e1) + " " + targetLang.linearize(e2)+".";
    	} else {
    		if (targetLang.hasLinearization(lemma))
    			return sourceLang.linearize(e1) + " - " + targetLang.linearize(e1);
    		else
    			return sourceLang.linearize(e1);
    	}
    }

	public String getInflectionTable(String lemma) {
		Concr targetLang = getTargetConcr();
		String cat = getGrammar().getFunctionType(lemma).getCategory();

		if (!targetLang.hasLinearization(lemma))
			return null;

		if (!targetLang.hasLinearization("Inflection"+cat))
			return null;

		Expr e = Expr.readExpr("MkDocument \"\" (Inflection"+cat+" "+lemma+") \"\"");
		String html =
			"<html><head><meta charset=\"UTF-8\"/></head><body>" +
			targetLang.linearize(e) +
			"</body>";

		return html;
	}

    public List<MorphoAnalysis> lookupMorpho(String sentence) {
        Log.e(TAG, "lookupMorpho " + getSourceConcr());
    	return getSourceConcr().lookupMorpho(sentence);
    }

    public CompletionInfo[] lookupWordPrefix(String prefix) {
    	PriorityQueue<FullFormEntry> queue = 
    		new PriorityQueue<FullFormEntry>(500, new Comparator<FullFormEntry>() {
				@Override
				public int compare(FullFormEntry lhs, FullFormEntry rhs) {
					return Double.compare(lhs.getProb(), rhs.getProb());
				}
			});
    	for (FullFormEntry entry : getSourceConcr().lookupWordPrefix(prefix)) {
    		queue.add(entry);
    		if (queue.size() >= 1000)
    			break;
    	}

    	CompletionInfo[] completions = new CompletionInfo[Math.min(queue.size(), 5)+1];
    	completions[0] = new CompletionInfo(0, 0, prefix);
    	for (int i = 1; i < completions.length; i++) {
    		completions[i] = new CompletionInfo(i,i,queue.poll().getForm());
    	}

    	if (completions.length > 1) {
	    	Arrays.sort(completions, 1, completions.length-1, new Comparator<CompletionInfo>() {
				@Override
				public int compare(CompletionInfo arg0, CompletionInfo arg1) {
					// TODO Auto-generated method stub
					return ((String) arg0.getText()).compareTo((String) arg1.getText());
				}
	    	});
    	}

    	return completions;
    }

	private PGF getGrammar() {
		try {
			mGrammarLoader.join();
		} catch (InterruptedException e) {
			Log.e(TAG, "Loading interrupted", e);
		}
		return mGrammarLoader.getGrammar();
	}

	private class GrammarLoader extends Thread {
		private PGF mPGF;
		
		public GrammarLoader() {
			mPGF = null;
		}

		public PGF getGrammar() {
			return mPGF;
		}

		public void run() {
			InputStream in = null;
			
		    try {
		    	in = mContext.getAssets().open(mGrammar);
		        Log.d(TAG, "Trying to open " + mGrammar);
		        long t1 = System.currentTimeMillis();
		        mPGF = PGF.readPGF(in);
		        long t2 = System.currentTimeMillis();
		        Log.d(TAG, mGrammar + " loaded ("+(t2-t1)+" ms)");		        
		    } catch (FileNotFoundException e) {
		        Log.e(TAG, "File not found", e);
		    } catch (IOException e) {
		        Log.e(TAG, "Error loading grammar", e);
		    } finally {
		    	if (in != null) {
		    		try {
		    			in.close();
		    		} catch (IOException e) {
		    			Log.e(TAG, "Error closing the stream", e);
		    		}
		    	}
		    }
		}
	}

	private class ConcrLoader extends Thread {
		private Language mLanguage;
		private Concr mConcr;

		public ConcrLoader(Language lang) {
			this.mLanguage = lang;
			this.mConcr = null;
		}

		public Language getLanguage() {
			return mLanguage;
		}
		
		public Concr getConcr() {
			return mConcr;
		}

		public void run() {
			try {
				mGrammarLoader.join();
			} catch (InterruptedException e) {
				Log.d(TAG, "interrupted", e);
			}

			InputStream in = null;

		    try {
		    	String name = mLanguage.getConcrete()+".pgf_c";
		    	in = mContext.getAssets().open(name);
		        Log.d(TAG, "Trying to load " + name);
		        long t1 = System.currentTimeMillis();
		        mConcr = mGrammarLoader.getGrammar().getLanguages().get(mLanguage.getConcrete());
		        mConcr.load(in);
		        long t2 = System.currentTimeMillis();
		        Log.d(TAG, name + " loaded ("+(t2-t1)+" ms)");
		    } catch (FileNotFoundException e) {
		        Log.e(TAG, "File not found", e);
		    } catch (IOException e) {
		        Log.e(TAG, "Error loading concrete", e);
		    } finally {
		    	if (in != null) {
		    		try {
		    			in.close();
		    		} catch (IOException e) {
		    			Log.e(TAG, "Error closing the stream", e);
		    		}
		    	}
		    }
		}
	}
}
